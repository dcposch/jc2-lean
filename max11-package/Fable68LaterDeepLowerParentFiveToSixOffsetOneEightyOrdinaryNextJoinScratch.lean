import Fable68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryJoinScratch

/-! # Closing the ordinary offset-180 face: row-zero `4` meets the loaded
I3 coefficient `2`

The joined ordinary offset-`180` packet left the contracted `(4,0,2,1,3)`
chart with the rigid I4 residual, the edge cubic, the three retained
first jets, the constant-`c`-jet pin `2*c₁² = c₂*(8*c₀ + 21*gamma)` and
the exhausted rows `7`, `6` (shadow), `5` on the row-zero tower.  This
file consumes the next two genuinely independent exact source rows
together: the literal row-zero coefficient `4` (expanded `299`) and the
first `epsilon`-loaded I3 coefficient `2` (expanded `120`), whose
literal content is extracted here for the first time.  Each row alone
only pins the subleading `A`-jet `a₁`: modulo the joined frontier the
loaded I3 coefficient `2` reduces to
`12*a₁*b²*d₁² + 8*b²*c₁³ + 72*b*d₁³ - 81*gamma*c₁*d₁² = 0`
while the loaded row-zero coefficient `4` reduces to
`84*a₁*b²*d₁² + 56*b²*c₁³ + 360*b*d₁³ - 567*gamma*c₁*d₁² = 0`.
The two `a₁`-pins are incompatible: seven times the first minus the
second leaves `144*b*d₁³ = 0` against the stored nonzeros `b` and `d₁`.
The ordinary nonzero-top face at offset `180` is therefore empty — a
full scalar closure, not a residual.  The reduction passes through five
staged pins, each dividing only by the stored nonzeros `b`, `c₂`, `d₁`:
the pinned quadratic `4*b²*c₂ = 9*d₁²`, the `e₁`-pin
`8*b*c₂*e₁ + 6*c₁²*d₁ = 9*gamma*c₂*d₁`, the `a₂`-pin
`4*a₂*b² + 18*c₁² = 27*gamma*c₂` (first exact use of the loaded I3
coefficient `3` beyond the join), the `e₀`-pin lifting the rigid I4
residual through the constant I4 jet, and the two row cores above.  No
sibling branch (pair-zero offset `180`, the offset-`120` small chart,
the aligned second-jet lane) is consumed, and the `gamma`-loaded
row-two coefficient `4` is not needed.  The wall disjunction now
survives only through its `zeta = 0` pair-zero arm. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryNextJoin68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- First coefficient of a product. -/
theorem mul_coeff_one_ordinaryOneEightyNextJoin68 (p q : k[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- Third coefficient of `A * A'` in the quartic chart. -/
theorem mul_derivative_coeff_three_ordinaryOneEightyNextJoin68
    (A : k[X]) :
    (A * derivative A).coeff 3 =
      4 * A.coeff 4 * A.coeff 0 + 4 * A.coeff 1 * A.coeff 3 +
        2 * A.coeff 2 ^ 2 := by
  have h := mul_coeff_three_oneTwentyOrdinaryNonzero68 A (derivative A)
  norm_num [coeff_derivative] at h
  linear_combination h

/-- The `epsilon`-loaded I3 coefficient `2` (expanded `120`) in
coordinates.  The row-one packet consumed the I3 value only through its
top jets; the second coefficient is extracted here for the first time
and is the first row seeing the `epsilon` load on the `c`-tower. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_two_ordinaryOneEightyNextJoin68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff 2 =
      (8 / 9 : k) *
        (-(A.coeff 1 * B.coeff 0 * d.coeff 1) -
          A.coeff 2 * B.coeff 0 * d.coeff 0 -
          B.coeff 0 ^ 2 * c.coeff 2 +
          3 * c.coeff 0 * e.coeff 2 + 3 * c.coeff 1 * e.coeff 1 +
          3 * c.coeff 2 * e.coeff 0) +
      (4 / 3 : k) * d.coeff 1 ^ 2 := by
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hAB1 : (A * B).coeff 1 = A.coeff 1 * B.coeff 0 := by
    have h := coeff_mul_C A 1 (B.coeff 0)
    rw [← hBC] at h
    exact h
  have hAB2 : (A * B).coeff 2 = A.coeff 2 * B.coeff 0 := by
    have h := coeff_mul_C A 2 (B.coeff 0)
    rw [← hBC] at h
    exact h
  have hABd2 : (A * B * d).coeff 2 =
      A.coeff 1 * B.coeff 0 * d.coeff 1 +
        A.coeff 2 * B.coeff 0 * d.coeff 0 := by
    have h := mul_coeff_two68 (A * B) d
    rw [hd2, hAB1, hAB2] at h
    linear_combination h
  have hB2c2 : (B ^ 2 * c).coeff 2 = B.coeff 0 ^ 2 * c.coeff 2 := by
    have heq : B ^ 2 * c = c * C (B.coeff 0 ^ 2) := by
      conv_lhs => rw [hBC]
      rw [← C_pow]
      ring
    rw [heq, coeff_mul_C]
    ring
  have hce2 : (c * e).coeff 2 =
      c.coeff 0 * e.coeff 2 + c.coeff 1 * e.coeff 1 +
        c.coeff 2 * e.coeff 0 := mul_coeff_two68 c e
  have hdsq2 : (d ^ 2).coeff 2 = d.coeff 1 ^ 2 := by
    rw [pow_two, mul_coeff_two68, hd2]
    ring
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd2, hB2c2, hce2, hdsq2]
  ring

/-- Homogeneous row-zero coefficient `4` (expanded `299`).  The two
already-consumed I4 jets kill the two high coefficients of `B*e+c*d`;
the survivors pair the third and fourth `A*A'` jets with the low
`B*e+c*d` jets, the odd `A'`-jets with the `c²` core and the full
`d`/`e` ladder, and the top `A`-jet with the constant `B²`-load. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_four_ordinaryOneEightyNextJoin68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hsecond : B.coeff 0 * e.coeff 2 +
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 4 =
      (4 / 27 : k) *
        (-((4 * A.coeff 0 * A.coeff 4 + 4 * A.coeff 1 * A.coeff 3 +
              2 * A.coeff 2 ^ 2) *
            (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
              c.coeff 0 * d.coeff 1)) -
          5 * (A.coeff 4 * A.coeff 1 + A.coeff 2 * A.coeff 3) *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) -
          A.coeff 4 * B.coeff 0 ^ 2 * d.coeff 1 +
          A.coeff 1 * B.coeff 0 * c.coeff 2 ^ 2 +
          4 * A.coeff 2 * B.coeff 0 * c.coeff 1 * c.coeff 2 +
          3 * A.coeff 3 * B.coeff 0 * c.coeff 1 ^ 2 +
          6 * A.coeff 3 * B.coeff 0 * c.coeff 0 * c.coeff 2 +
          8 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 1 -
          3 * ((A.coeff 1 * d.coeff 1 + 2 * A.coeff 2 * d.coeff 0) *
              e.coeff 3 +
            (2 * A.coeff 2 * d.coeff 1 + 3 * A.coeff 3 * d.coeff 0) *
              e.coeff 2 +
            (3 * A.coeff 3 * d.coeff 1 + 4 * A.coeff 4 * d.coeff 0) *
              e.coeff 1 +
            4 * A.coeff 4 * d.coeff 1 * e.coeff 0) +
          9 * B.coeff 0 * c.coeff 2 * e.coeff 3 -
          6 * c.coeff 2 ^ 2 * d.coeff 1) := by
  let F : k[X] := B * e + c * d
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hF : F.natDegree ≤ 3 := by simp only [F]; compute_degree; omega
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hderB : derivative B = 0 := derivative_eq_zero.mpr (by omega)
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
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
  have hG4 := mul_derivative_coeff_four_ordinaryOneEightyJoin68 A hA
  have hG3 := mul_derivative_coeff_three_ordinaryOneEightyNextJoin68 A
  have hAAF : (A * derivative A * F).coeff 4 =
      (4 * A.coeff 4 * A.coeff 0 + 4 * A.coeff 1 * A.coeff 3 +
          2 * A.coeff 2 ^ 2) *
          (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
            c.coeff 0 * d.coeff 1) +
        (5 * A.coeff 4 * A.coeff 1 + 5 * A.coeff 2 * A.coeff 3) *
          (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68
      (A * derivative A) F
    rw [hF2, hF3, hF4, hG3, hG4, hF0, hF1] at h
    linear_combination h
  have hd'C : derivative d = C (d.coeff 1) := by
    have hdeg : (derivative d).natDegree ≤ 0 :=
      (natDegree_derivative_le d).trans (by omega)
    have h0 : (derivative d).coeff 0 = d.coeff 1 := by
      rw [coeff_derivative]
      norm_num
    exact (eq_C_of_natDegree_le_zero hdeg).trans (by rw [h0])
  have hABsq : (A * B ^ 2 * derivative d).coeff 4 =
      A.coeff 4 * B.coeff 0 ^ 2 * d.coeff 1 := by
    have heq : A * B ^ 2 * derivative d =
        A * C (B.coeff 0 ^ 2 * d.coeff 1) := by
      conv_lhs => rw [hBC, hd'C]
      rw [← C_pow, mul_assoc, ← C_mul]
    rw [heq, coeff_mul_C]
    ring
  have hlow4 : (A * B * derivative B * d).natDegree < 4 := by
    rw [hderB, mul_zero, zero_mul, natDegree_zero]
    norm_num
  have hA'Bdeg : (derivative A * B).natDegree ≤ 3 := by
    compute_degree
    omega
  have hA'B4 : (derivative A * B).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hA'B0 : (derivative A * B).coeff 0 = A.coeff 1 * B.coeff 0 := by
    rw [mul_coeff_zero, coeff_derivative]
    norm_num
  have hA'B1 : (derivative A * B).coeff 1 = 2 * A.coeff 2 * B.coeff 0 := by
    have h := coeff_mul_C (derivative A) 1 (B.coeff 0)
    rw [← hBC] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hA'B2 : (derivative A * B).coeff 2 = 3 * A.coeff 3 * B.coeff 0 := by
    have h := coeff_mul_C (derivative A) 2 (B.coeff 0)
    rw [← hBC] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hA'B3 : (derivative A * B).coeff 3 = 4 * A.coeff 4 * B.coeff 0 := by
    have h := coeff_mul_C (derivative A) 3 (B.coeff 0)
    rw [← hBC] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hcsqdeg : (c ^ 2).natDegree ≤ 4 := by
    compute_degree
    omega
  have hcsq4 : (c ^ 2).coeff 4 = c.coeff 2 ^ 2 := by
    have h := coeff_mul_at_bounds68 c c 2 2 hc hc
    norm_num at h
    rw [pow_two]
    linear_combination h
  have hcsq3 : (c ^ 2).coeff 3 = 2 * c.coeff 1 * c.coeff 2 := by
    rw [pow_two, mul_coeff_three_oneTwentyOrdinaryNonzero68, hc3]
    ring
  have hcsq2 : (c ^ 2).coeff 2 =
      c.coeff 1 ^ 2 + 2 * c.coeff 0 * c.coeff 2 := by
    rw [pow_two, mul_coeff_two68]
    ring
  have hcsq1 : (c ^ 2).coeff 1 = 2 * c.coeff 0 * c.coeff 1 := by
    rw [pow_two, mul_coeff_one_ordinaryOneEightyNextJoin68]
    ring
  have hcsq0 : (c ^ 2).coeff 0 = c.coeff 0 ^ 2 := by
    rw [pow_two, mul_coeff_zero]
    ring
  have hBc2 : (derivative A * B * c ^ 2).coeff 4 =
      A.coeff 1 * B.coeff 0 * c.coeff 2 ^ 2 +
        4 * A.coeff 2 * B.coeff 0 * c.coeff 1 * c.coeff 2 +
        3 * A.coeff 3 * B.coeff 0 * c.coeff 1 ^ 2 +
        6 * A.coeff 3 * B.coeff 0 * c.coeff 0 * c.coeff 2 +
        8 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 1 := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68
      (derivative A * B) (c ^ 2)
    rw [hA'B4, hA'B0, hA'B1, hA'B2, hA'B3, hcsq0, hcsq1, hcsq2, hcsq3,
      hcsq4] at h
    linear_combination h
  have hA'dDeg : (derivative A * d).natDegree ≤ 4 := by
    compute_degree
    omega
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
  have hA'd2 : (derivative A * d).coeff 2 =
      2 * A.coeff 2 * d.coeff 1 + 3 * A.coeff 3 * d.coeff 0 := by
    have h := mul_coeff_two68 (derivative A) d
    rw [hd2] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hA'd1 : (derivative A * d).coeff 1 =
      A.coeff 1 * d.coeff 1 + 2 * A.coeff 2 * d.coeff 0 := by
    have h := mul_coeff_one_ordinaryOneEightyNextJoin68 (derivative A) d
    norm_num [coeff_derivative] at h
    linear_combination h
  have hde : (derivative A * d * e).coeff 4 =
      (A.coeff 1 * d.coeff 1 + 2 * A.coeff 2 * d.coeff 0) * e.coeff 3 +
        (2 * A.coeff 2 * d.coeff 1 + 3 * A.coeff 3 * d.coeff 0) *
          e.coeff 2 +
        (3 * A.coeff 3 * d.coeff 1 + 4 * A.coeff 4 * d.coeff 0) *
          e.coeff 1 +
        4 * A.coeff 4 * d.coeff 1 * e.coeff 0 := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68
      (derivative A * d) e
    rw [he4, hA'd1, hA'd2, hA'd3, hA'd4] at h
    linear_combination h
  have hdere : (derivative e).natDegree ≤ 2 := by compute_degree; omega
  have hce'4 : (c * derivative e).coeff 4 =
      3 * c.coeff 2 * e.coeff 3 := by
    have h := coeff_mul_at_bounds68 c (derivative e) 2 2 hc hdere
    norm_num [coeff_derivative] at h
    linear_combination h
  have hBce : (B * c * derivative e).coeff 4 =
      3 * B.coeff 0 * c.coeff 2 * e.coeff 3 := by
    have heq : B * c * derivative e =
        c * derivative e * C (B.coeff 0) := by
      conv_lhs => rw [hBC]
      ring
    rw [heq, coeff_mul_C, hce'4]
    ring
  have hlow8 : (B * d * derivative d).natDegree < 4 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 4 := by
    rw [hderB, zero_mul, natDegree_zero]
    norm_num
  have hderc : (derivative c).natDegree ≤ 1 := by compute_degree; omega
  have hccdeg : (c * derivative c).natDegree ≤ 3 := by
    compute_degree
    omega
  have hcc'3 : (c * derivative c).coeff 3 = 2 * c.coeff 2 ^ 2 := by
    have h := coeff_mul_at_bounds68 c (derivative c) 2 1 hc hderc
    norm_num [coeff_derivative] at h
    linear_combination h
  have hccd4 : (c * derivative c * d).coeff 4 =
      2 * c.coeff 2 ^ 2 * d.coeff 1 := by
    have h := coeff_mul_at_bounds68 (c * derivative c) d 3 1 hccdeg hd
    norm_num at h
    rw [hcc'3] at h
    linear_combination h
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
  simp only [coeff_smul, coeff_add, coeff_sub, coeff_neg, hAAF, hABsq,
    hBc2, hde, hBce, hccd4, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9]
  ring

/-- Exact literal load at the same coefficient: the `epsilon` load sits
on the fourth `A*A'` jet and the top `A`-jet against `d₁`, the `gamma`
loads on the odd `A'`-jets against the `c`-tower and on the third and
fourth `A*A'` jets against the `d`-jets. -/
theorem cubicLoadRowZeroPolynomial68_coeff_four_ordinaryOneEightyNextJoin68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 4 =
      (2 / 3 : k) * gamma * A.coeff 3 * B.coeff 0 * c.coeff 2 +
        (8 / 9 : k) * gamma * A.coeff 4 * B.coeff 0 * c.coeff 1 -
        (5 / 9 : k) * epsilon *
          (A.coeff 1 * A.coeff 4 + A.coeff 2 * A.coeff 3) * B.coeff 0 -
        (4 / 3 : k) * epsilon * A.coeff 4 * d.coeff 1 -
        (2 / 9 : k) * gamma *
          ((4 * A.coeff 0 * A.coeff 4 + 4 * A.coeff 1 * A.coeff 3 +
              2 * A.coeff 2 ^ 2) * d.coeff 1 +
            5 * (A.coeff 1 * A.coeff 4 + A.coeff 2 * A.coeff 3) *
              d.coeff 0) := by
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
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hA5 : A.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hc4 : c.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hG4 := mul_derivative_coeff_four_ordinaryOneEightyJoin68 A hA
  have hG3 := mul_derivative_coeff_three_ordinaryOneEightyNextJoin68 A
  have hABA' : (A * B * derivative A).coeff 4 =
      (5 * A.coeff 4 * A.coeff 1 + 5 * A.coeff 2 * A.coeff 3) *
        B.coeff 0 := by
    have heq : A * B * derivative A =
        A * derivative A * C (B.coeff 0) := by
      conv_lhs => rw [hBC]
      ring
    rw [heq, coeff_mul_C, hG4]
  have hAAd : (A * derivative A * d).coeff 4 =
      (4 * A.coeff 4 * A.coeff 0 + 4 * A.coeff 1 * A.coeff 3 +
          2 * A.coeff 2 ^ 2) * d.coeff 1 +
        (5 * A.coeff 4 * A.coeff 1 + 5 * A.coeff 2 * A.coeff 3) *
          d.coeff 0 := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68
      (A * derivative A) d
    rw [hd2, hd3, hd4, hG3, hG4] at h
    linear_combination h
  have hA'c4 : (derivative A * c).coeff 4 =
      3 * A.coeff 3 * c.coeff 2 + 4 * A.coeff 4 * c.coeff 1 := by
    have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68
      (derivative A) c
    rw [hc3, hc4] at h
    norm_num [coeff_derivative, hA5] at h
    linear_combination h
  have hBA'c : (B * derivative A * c).coeff 4 =
      (3 * A.coeff 3 * c.coeff 2 + 4 * A.coeff 4 * c.coeff 1) *
        B.coeff 0 := by
    have heq : B * derivative A * c =
        derivative A * c * C (B.coeff 0) := by
      conv_lhs => rw [hBC]
      ring
    rw [heq, coeff_mul_C, hA'c4]
  have hdA' : (d * derivative A).coeff 4 =
      4 * A.coeff 4 * d.coeff 1 := by
    have h := coeff_mul_at_bounds68 d (derivative A) 1 3 hd hderA
    norm_num [coeff_derivative] at h
    linear_combination h
  have hlowBe : (B * derivative e).natDegree < 4 := by
    compute_degree
    omega
  have hlowdc : (d * derivative c).natDegree < 4 := by
    compute_degree
    omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 4 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, hABA', hAAd,
    hBA'c, hdA',
    coeff_eq_zero_of_natDegree_lt hlowBe,
    coeff_eq_zero_of_natDegree_lt hlowdc]
  ring

/-- Scalar closure of the ordinary offset-`180` face.  Modulo the joined
frontier the loaded I3 coefficient `2` and the loaded row-zero
coefficient `4` each pin the subleading `A`-jet `a₁`, but incompatibly:
seven times the first core minus the second leaves `144*b*d₁³ = 0`
against the stored nonzeros.  The reduction stages the pinned quadratic,
the `e₁`-pin, the `a₂`-pin, and the `e₀`-pin, dividing only by the
stored nonzeros `b`, `c₂`, `d₁`. -/
theorem fiveToSix_ordinaryOneEightyNextJoin_closure_false68
    (a a₀ a₁ a₂ a₃ b c₀ c₁ c₂ d₀ d₁ e₀ e₁ e₂ e₃ gamma epsilon i4 : k)
    (hb : b ≠ 0) (hcTop : c₂ ≠ 0) (hx : d₁ ≠ 0)
    (hface : b * e₃ + c₂ * d₁ = 0)
    (hdisc : a * b ^ 2 + 3 * c₂ ^ 2 = 0)
    (hedge : 9 * e₃ ^ 2 - 4 * c₂ ^ 3 = 0)
    (hfirst : (8 / 3 : k) * (b * e₁ + c₁ * d₀ + c₀ * d₁) +
      4 * gamma * d₁ = 0)
    (hconstant : (-8 / 27 : k) * b ^ 3 +
      (8 / 3 : k) * (b * e₀ + c₀ * d₀) +
      2 * epsilon * b + 4 * gamma * d₀ = i4)
    (hrigid : 27 * a * i4 + 32 * a * b ^ 3 + 216 * d₁ * e₃ = 0)
    (hT1 : a₃ * b ^ 2 + 6 * c₁ * c₂ = 0)
    (hT2 : 2 * c₂ * d₀ - c₁ * d₁ = 0)
    (hT3 : 2 * b * e₂ + 3 * c₁ * d₁ = 0)
    (hJ3 : (8 / 9 : k) * (-(a₃ * b * d₀) - a₂ * b * d₁ +
        3 * c₀ * e₃ + 3 * c₁ * e₂ + 3 * c₂ * e₁) +
      4 * gamma * e₃ = 0)
    (hGain : 2 * c₁ ^ 2 - c₂ * (8 * c₀ + 21 * gamma) = 0)
    (hJ2 : (8 / 9 : k) *
        (-(a₁ * b * d₁) - a₂ * b * d₀ - b ^ 2 * c₂ +
          3 * c₀ * e₂ + 3 * c₁ * e₁ + 3 * c₂ * e₀) +
      (4 / 3 : k) * d₁ ^ 2 + 2 * epsilon * c₂ + 4 * gamma * e₂ = 0)
    (hrow4 : (4 / 27 : k) *
        (-((4 * a₀ * a + 4 * a₁ * a₃ + 2 * a₂ ^ 2) *
            (b * e₁ + c₁ * d₀ + c₀ * d₁)) -
          5 * (a * a₁ + a₂ * a₃) * (b * e₀ + c₀ * d₀) -
          a * b ^ 2 * d₁ +
          a₁ * b * c₂ ^ 2 + 4 * a₂ * b * c₁ * c₂ + 3 * a₃ * b * c₁ ^ 2 +
          6 * a₃ * b * c₀ * c₂ + 8 * a * b * c₀ * c₁ -
          3 * ((a₁ * d₁ + 2 * a₂ * d₀) * e₃ +
            (2 * a₂ * d₁ + 3 * a₃ * d₀) * e₂ +
            (3 * a₃ * d₁ + 4 * a * d₀) * e₁ +
            4 * a * d₁ * e₀) +
          9 * b * c₂ * e₃ - 6 * c₂ ^ 2 * d₁) +
        ((2 / 3 : k) * gamma * a₃ * b * c₂ +
          (8 / 9 : k) * gamma * a * b * c₁ -
          (5 / 9 : k) * epsilon * (a₁ * a + a₂ * a₃) * b -
          (4 / 3 : k) * epsilon * a * d₁ -
          (2 / 9 : k) * gamma *
            ((4 * a₀ * a + 4 * a₁ * a₃ + 2 * a₂ ^ 2) * d₁ +
              5 * (a₁ * a + a₂ * a₃) * d₀)) = 0) :
    False := by
  have hpins : c₂ ^ 2 * (4 * b ^ 2 * c₂ - 9 * d₁ ^ 2) = 0 := by
    linear_combination (-(b ^ 2)) * hedge +
      (9 * (b * e₃ - c₂ * d₁)) * hface
  have hpin : 4 * b ^ 2 * c₂ - 9 * d₁ ^ 2 = 0 :=
    (mul_eq_zero.mp hpins).resolve_left (pow_ne_zero 2 hcTop)
  have hE1 : 8 * b * c₂ * e₁ + 6 * c₁ ^ 2 * d₁ -
      9 * c₂ * d₁ * gamma = 0 := by
    linear_combination (3 * c₂ : k) * hfirst - (4 * c₁ : k) * hT2 +
      (d₁ : k) * hGain
  have hA2d : d₁ * (4 * a₂ * b ^ 2 + 18 * c₁ ^ 2 -
      27 * c₂ * gamma) = 0 := by
    linear_combination ((-9 * b) / 2 : k) * hJ3 +
      ((3) / 2 : k) * hE1 +
      (6 * c₁ : k) * hT3 +
      (12 * c₀ + 18 * gamma : k) * hface +
      (-4 * d₀ : k) * hT1 +
      (12 * c₁ : k) * hT2 +
      ((3 * d₁) / 2 : k) * hGain
  have hA2 : 4 * a₂ * b ^ 2 + 18 * c₁ ^ 2 - 27 * c₂ * gamma = 0 :=
    (mul_eq_zero.mp hA2d).resolve_left hx
  have hE0 : 16 * b ^ 3 * c₂ ^ 2 + 48 * b * c₂ ^ 2 * e₀ +
      36 * b * c₂ ^ 2 * epsilon + 48 * b * c₂ * d₁ ^ 2 +
      6 * c₁ ^ 3 * d₁ - 27 * c₁ * c₂ * d₁ * gamma = 0 := by
    linear_combination ((-2 * b ^ 2) / 9 : k) * hrigid +
      (48 * b * d₁ : k) * hface +
      ((16 * b ^ 3 + 48 * b * e₀ + 36 * b * epsilon + 48 * c₀ * d₀ +
        72 * d₀ * gamma) / 3 : k) * hdisc +
      (-24 * c₀ * c₂ - 36 * c₂ * gamma : k) * hT2 +
      (3 * c₁ * d₁ : k) * hGain +
      (-6 * a * b ^ 2 : k) * hconstant
  have hR1d : d₁ * (12 * a₁ * b ^ 2 * d₁ ^ 2 + 8 * b ^ 2 * c₁ ^ 3 +
      72 * b * d₁ ^ 3 - 81 * c₁ * d₁ ^ 2 * gamma) = 0 := by
    linear_combination (-6 * b ^ 3 * c₂ : k) * hJ2 +
      ((b ^ 2) / 3 : k) * hE0 +
      (2 * b ^ 2 * c₁ : k) * hE1 +
      (8 * b ^ 2 * c₀ * c₂ + 12 * b ^ 2 * c₂ * gamma : k) * hT3 +
      ((-4 * b ^ 2 * c₂ * d₀) / 3 : k) * hA2 +
      (12 * b ^ 2 * c₁ ^ 2 - 18 * b ^ 2 * c₂ * gamma : k) * hT2 +
      (3 * b ^ 2 * c₁ * d₁ : k) * hGain +
      ((-4 * a₁ * b ^ 2 * d₁ - 8 * b ^ 3 * c₂ - 24 * b * d₁ ^ 2 +
        27 * c₁ * d₁ * gamma) / 3 : k) * hpin
  have hR1 : 12 * a₁ * b ^ 2 * d₁ ^ 2 + 8 * b ^ 2 * c₁ ^ 3 +
      72 * b * d₁ ^ 3 - 81 * c₁ * d₁ ^ 2 * gamma = 0 :=
    (mul_eq_zero.mp hR1d).resolve_left hx
  have hR2d : d₁ ^ 6 * (84 * a₁ * b ^ 2 * d₁ ^ 2 + 56 * b ^ 2 * c₁ ^ 3 +
      360 * b * d₁ ^ 3 - 567 * c₁ * d₁ ^ 2 * gamma) = 0 := by
    linear_combination ((-64 * b ^ 9 * c₂ ^ 2) / 27 : k) * hrow4 +
      ((-80 * a₁ * a * b ^ 9 - 80 * a₂ * a₃ * b ^ 9 -
        192 * a * b ^ 8 * d₁) / 2187 : k) * hE0 +
      ((-128 * a₀ * a * b ^ 9 * c₂ - 128 * a₁ * a₃ * b ^ 9 * c₂ -
        64 * a₂ ^ 2 * b ^ 9 * c₂ - 288 * a₃ * b ^ 8 * c₂ * d₁ -
        384 * a * b ^ 8 * c₂ * d₀) / 729 : k) * hE1 +
      ((-256 * a₂ * b ^ 8 * c₂ ^ 2 * d₁ -
        384 * a₃ * b ^ 8 * c₂ ^ 2 * d₀) / 243 : k) * hT3 +
      ((-256 * a₁ * b ^ 8 * c₂ ^ 2 * d₁ - 512 * a₂ * b ^ 8 * c₂ ^ 2 * d₀ +
        768 * b ^ 9 * c₂ ^ 3) / 243 : k) * hface +
      ((-384 * a₂ * b ^ 7 * c₀ * c₂ ^ 2 * d₁ +
        288 * a₂ * b ^ 7 * c₁ ^ 2 * c₂ * d₁ -
        384 * a₂ * b ^ 7 * c₁ * c₂ ^ 2 * d₀ -
        1008 * a₂ * b ^ 7 * c₂ ^ 2 * d₁ * gamma +
        320 * a₃ * b ^ 10 * c₂ ^ 2 + 960 * a₃ * b ^ 8 * c₂ * d₁ ^ 2 -
        960 * a₃ * b ^ 7 * c₀ * c₂ ^ 2 * d₀ +
        120 * a₃ * b ^ 7 * c₁ ^ 3 * d₁ -
        540 * a₃ * b ^ 7 * c₁ * c₂ * d₁ * gamma -
        1440 * a₃ * b ^ 7 * c₂ ^ 2 * d₀ * gamma +
        768 * b ^ 8 * c₁ * c₂ ^ 3 + 1728 * b ^ 6 * c₁ * c₂ ^ 2 * d₁ ^ 2 +
        1152 * b ^ 6 * c₂ ^ 3 * d₀ * d₁ +
        1728 * b ^ 5 * c₀ * c₁ ^ 2 * c₂ ^ 2 * d₁ -
        2592 * b ^ 5 * c₀ * c₂ ^ 3 * d₁ * gamma -
        1296 * b ^ 5 * c₁ ^ 4 * c₂ * d₁ +
        1728 * b ^ 5 * c₁ ^ 3 * c₂ ^ 2 * d₀ +
        6480 * b ^ 5 * c₁ ^ 2 * c₂ ^ 2 * d₁ * gamma -
        2592 * b ^ 5 * c₁ * c₂ ^ 3 * d₀ * gamma -
        6804 * b ^ 5 * c₂ ^ 3 * d₁ * gamma ^ 2) / 2187 : k) * hA2 +
      ((-1024 * a₁ * b ^ 7 * c₀ * c₂ ^ 2 * d₁ +
        768 * a₁ * b ^ 7 * c₁ ^ 2 * c₂ * d₁ -
        1024 * a₁ * b ^ 7 * c₁ * c₂ ^ 2 * d₀ -
        2688 * a₁ * b ^ 7 * c₂ ^ 2 * d₁ * gamma +
        1536 * b ^ 8 * c₀ * c₂ ^ 3 - 1152 * b ^ 8 * c₁ ^ 2 * c₂ ^ 2 +
        4032 * b ^ 8 * c₂ ^ 3 * gamma -
        4032 * b ^ 6 * c₁ ^ 2 * c₂ * d₁ ^ 2 +
        3456 * b ^ 6 * c₁ * c₂ ^ 2 * d₀ * d₁ +
        6048 * b ^ 6 * c₂ ^ 2 * d₁ ^ 2 * gamma +
        5760 * b ^ 5 * c₀ * c₁ ^ 2 * c₂ ^ 2 * d₀ -
        8640 * b ^ 5 * c₀ * c₂ ^ 3 * d₀ * gamma -
        720 * b ^ 5 * c₁ ^ 5 * d₁ +
        4320 * b ^ 5 * c₁ ^ 3 * c₂ * d₁ * gamma +
        8640 * b ^ 5 * c₁ ^ 2 * c₂ ^ 2 * d₀ * gamma -
        4860 * b ^ 5 * c₁ * c₂ ^ 2 * d₁ * gamma ^ 2 -
        12960 * b ^ 5 * c₂ ^ 3 * d₀ * gamma ^ 2) / 729 : k) * hT1 +
      ((-3072 * a₀ * b ^ 7 * c₀ * c₂ ^ 2 * d₁ +
        2304 * a₀ * b ^ 7 * c₁ ^ 2 * c₂ * d₁ -
        3072 * a₀ * b ^ 7 * c₁ * c₂ ^ 2 * d₀ -
        8064 * a₀ * b ^ 7 * c₂ ^ 2 * d₁ * gamma +
        1280 * a₁ * b ^ 10 * c₂ ^ 2 + 3840 * a₁ * b ^ 8 * c₂ * d₁ ^ 2 -
        3840 * a₁ * b ^ 7 * c₀ * c₂ ^ 2 * d₀ +
        480 * a₁ * b ^ 7 * c₁ ^ 3 * d₁ -
        2160 * a₁ * b ^ 7 * c₁ * c₂ * d₁ * gamma -
        5760 * a₁ * b ^ 7 * c₂ ^ 2 * d₀ * gamma +
        2304 * b ^ 9 * c₂ ^ 2 * d₁ + 6144 * b ^ 8 * c₀ * c₁ * c₂ ^ 2 +
        4608 * b ^ 8 * c₁ * c₂ ^ 2 * gamma + 9216 * b ^ 7 * c₂ * d₁ ^ 3 +
        1152 * b ^ 6 * c₁ ^ 3 * d₁ ^ 2 +
        6912 * b ^ 6 * c₁ ^ 2 * c₂ * d₀ * d₁ -
        5184 * b ^ 6 * c₁ * c₂ * d₁ ^ 2 * gamma -
        10368 * b ^ 6 * c₂ ^ 2 * d₀ * d₁ * gamma) / 2187 : k) * hdisc +
      ((512 * a₀ * b ^ 7 * c₁ * c₂ ^ 3 + 640 * a₁ * b ^ 7 * c₀ * c₂ ^ 3 +
        1024 * a₁ * b ^ 7 * c₁ ^ 2 * c₂ ^ 2 +
        960 * a₁ * b ^ 7 * c₂ ^ 3 * gamma -
        5760 * b ^ 6 * c₁ ^ 2 * c₂ ^ 2 * d₁ +
        3456 * b ^ 6 * c₂ ^ 3 * d₁ * gamma -
        5760 * b ^ 5 * c₀ * c₁ ^ 3 * c₂ ^ 2 +
        8640 * b ^ 5 * c₀ * c₁ * c₂ ^ 3 * gamma -
        1728 * b ^ 5 * c₁ ^ 5 * c₂ -
        3456 * b ^ 5 * c₁ ^ 3 * c₂ ^ 2 * gamma +
        9072 * b ^ 5 * c₁ * c₂ ^ 3 * gamma ^ 2) / 243 : k) * hT2 +
      ((-128 * a₀ * b ^ 7 * c₂ ^ 3 * d₁ -
        336 * a₁ * b ^ 7 * c₁ * c₂ ^ 2 * d₁ +
        640 * b ^ 8 * c₁ * c₂ ^ 3 + 1152 * b ^ 5 * c₁ ^ 4 * c₂ * d₁ -
        2376 * b ^ 5 * c₁ ^ 2 * c₂ ^ 2 * d₁ * gamma +
        972 * b ^ 5 * c₂ ^ 3 * d₁ * gamma ^ 2) / 243 : k) * hGain +
      ((-256 * a₁ * b ^ 8 * c₂ ^ 3 - 1344 * a₁ * b ^ 6 * c₂ ^ 2 * d₁ ^ 2 -
        3024 * a₁ * b ^ 4 * c₂ * d₁ ^ 4 - 6804 * a₁ * b ^ 2 * d₁ ^ 6 -
        1536 * b ^ 7 * c₂ ^ 3 * d₁ - 384 * b ^ 6 * c₁ ^ 3 * c₂ ^ 2 +
        4608 * b ^ 6 * c₁ * c₂ ^ 3 * gamma - 5760 * b ^ 5 * c₂ ^ 2 * d₁ ^ 3 -
        2016 * b ^ 4 * c₁ ^ 3 * c₂ * d₁ ^ 2 +
        9072 * b ^ 4 * c₁ * c₂ ^ 2 * d₁ ^ 2 * gamma -
        12960 * b ^ 3 * c₂ * d₁ ^ 5 - 4536 * b ^ 2 * c₁ ^ 3 * d₁ ^ 4 +
        20412 * b ^ 2 * c₁ * c₂ * d₁ ^ 4 * gamma - 29160 * b * d₁ ^ 7 +
        45927 * c₁ * d₁ ^ 6 * gamma) / 729 : k) * hpin
  have hR2 : 84 * a₁ * b ^ 2 * d₁ ^ 2 + 56 * b ^ 2 * c₁ ^ 3 +
      360 * b * d₁ ^ 3 - 567 * c₁ * d₁ ^ 2 * gamma = 0 :=
    (mul_eq_zero.mp hR2d).resolve_left (pow_ne_zero 6 hx)
  have hcontra : (144 : k) * (b * d₁ ^ 3) = 0 := by
    linear_combination 7 * hR1 - hR2
  rcases mul_eq_zero.mp hcontra with h144 | hbd
  · exact absurd h144 (by norm_num)
  · exact mul_ne_zero hb (pow_ne_zero 3 hx) hbd

set_option maxHeartbeats 15000000 in
/-- Elimination of the joined ordinary offset-`180` source face.  On top
of the joined frontier — whose gain is re-derived by feeding the
row-zero coefficient `5` through the imported join packet — the literal
row-zero coefficient `4` (expanded `299`) and the `epsilon`-loaded I3
coefficient `2` (expanded `120`) pin the subleading `A`-jet `a₁`
incompatibly, leaving `144*b*d₁³ = 0` against the stored nonzeros.  The
ordinary nonzero-top face at offset `180` is empty; no sibling branch
(pair-zero offset `180`, the offset-`120` small chart, the aligned
second-jet lane) is touched. -/
theorem fiveToSix_offsetOneEighty_ordinaryNextJoin_source_false68
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
    (hedge : 9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0)
    (hjetDisc : A.coeff 3 * B.coeff 0 ^ 2 +
      6 * c.coeff 1 * c.coeff 2 = 0)
    (hjetEdge : 2 * c.coeff 2 * d.coeff 0 -
      c.coeff 1 * d.coeff 1 = 0)
    (hjetLoad : 2 * B.coeff 0 * e.coeff 2 +
      3 * c.coeff 1 * d.coeff 1 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowZero :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C0 D0 E0) D0 E0).coeff 5 = 0)
    (hrowZeroFour :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C0 D0 E0) D0 E0).coeff 4 = 0) :
    False := by
  obtain ⟨-, -, -, -, -, -, hGain, -⟩ :=
    fiveToSix_offsetOneEighty_ordinaryJoin_source_packet68
      alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd he ha hb hcTop
      hx hy hface hdisc hi4rigid hedge hjetDisc hjetEdge hjetLoad hi4 hi3
      hrowZero
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
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hB2deg : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hB23 : (B ^ 2).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  have hB22 : (B ^ 2).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  have hI3J : secondaryResidualInvariantThreePolynomial68 A B c d e +
      (2 * epsilon : k) • c + (4 * gamma : k) • e -
      (2 / 3 * gamma : k) • B ^ 2 = C i3 := by
    have hres := hi3
    rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
      at hres
    simp only [zero_smul, zero_add] at hres
    simpa only [add_zero] using hres
  have h3 := congrArg (fun p : k[X] => p.coeff 3) hI3J
  norm_num [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_C,
    hc3, hB23] at h3
  have hJ3v :=
    secondaryResidualInvariantThreePolynomial68_coeff_three_ordinaryOneEightyJoin68
      A B c d e hA hB hc hd he
  have hJ3s : (8 / 9 : k) *
      (-(A.coeff 3 * B.coeff 0 * d.coeff 0) -
        A.coeff 2 * B.coeff 0 * d.coeff 1 +
        3 * c.coeff 0 * e.coeff 3 + 3 * c.coeff 1 * e.coeff 2 +
        3 * c.coeff 2 * e.coeff 1) +
      4 * gamma * e.coeff 3 = 0 := by
    linear_combination h3 - hJ3v
  have h2 := congrArg (fun p : k[X] => p.coeff 2) hI3J
  norm_num [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, coeff_C,
    hB22] at h2
  have hJ2v :=
    secondaryResidualInvariantThreePolynomial68_coeff_two_ordinaryOneEightyNextJoin68
      A B c d e hA hB hc hd he
  have hJ2s : (8 / 9 : k) *
      (-(A.coeff 1 * B.coeff 0 * d.coeff 1) -
        A.coeff 2 * B.coeff 0 * d.coeff 0 -
        B.coeff 0 ^ 2 * c.coeff 2 +
        3 * c.coeff 0 * e.coeff 2 + 3 * c.coeff 1 * e.coeff 1 +
        3 * c.coeff 2 * e.coeff 0) +
      (4 / 3 : k) * d.coeff 1 ^ 2 +
      2 * epsilon * c.coeff 2 + 4 * gamma * e.coeff 2 = 0 := by
    linear_combination h2 - hJ2v
  let C0 : k[X] := (1 / 3 : k) • A ^ 2 + c
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B C0 D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B C0 D0 E0) D0 E0).coeff 4 = 0 at hrowZeroFour
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon 0 eta A B c D0 e
  have hhom : cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
      secondaryResidualRowZeroPolynomial68 A B c d e := by
    simpa only [D0] using
      cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e
  have hres4 :=
    secondaryResidualRowZeroPolynomial68_coeff_four_ordinaryOneEightyNextJoin68
      A B c d e hA hB hc hd he hface hsecond
  have hload4 :=
    cubicLoadRowZeroPolynomial68_coeff_four_ordinaryOneEightyNextJoin68
      alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add, hhom, hres4, hload4] at hrowZeroFour
  exact fiveToSix_ordinaryOneEightyNextJoin_closure_false68
    (A.coeff 4) (A.coeff 0) (A.coeff 1) (A.coeff 2) (A.coeff 3)
    (B.coeff 0) (c.coeff 0) (c.coeff 1) (c.coeff 2)
    (d.coeff 0) (d.coeff 1)
    (e.coeff 0) (e.coeff 1) (e.coeff 2) (e.coeff 3)
    gamma epsilon i4 hb hcTop hx hface hdisc hedge hfirst hconstant
    hi4rigid hjetDisc hjetEdge hjetLoad hJ3s hGain hJ2s
    (by linear_combination hrowZeroFour)

#print axioms mul_coeff_one_ordinaryOneEightyNextJoin68
#print axioms mul_derivative_coeff_three_ordinaryOneEightyNextJoin68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_two_ordinaryOneEightyNextJoin68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_four_ordinaryOneEightyNextJoin68
#print axioms cubicLoadRowZeroPolynomial68_coeff_four_ordinaryOneEightyNextJoin68
#print axioms fiveToSix_ordinaryOneEightyNextJoin_closure_false68
#print axioms fiveToSix_offsetOneEighty_ordinaryNextJoin_source_false68

end LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryNextJoin68

end Max11DegreeRoutes
