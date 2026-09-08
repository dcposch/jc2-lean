import Fable68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryRowTwoScratch
import Fable68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryNonzeroNextScratch

/-! # Joining the ordinary offset-180 packets and consuming row-zero `5`

Both preserved ordinary nonzero-discriminant packets of the
`(n,g)=(120,360)` wall live on the offset-`180` face in the contracted
`(4,0,2,1,3)` chart, over the same source variables: the row-two packet
carries the rigid I4 residual, the edge cubic `9*e₃² = 4*c₂³` and the
exact constant-I3 row, while the continued row-zero packet added the
discriminant first jet `a₃*b² + 6*c₁*c₂ = 0` and the edge alignments
`2*c₂*d₀ = c₁*d₁`, `2*b*e₂ + 3*c₁*d₁ = 0`.  This file joins the two
frontiers into a single packet and consumes the next genuinely
independent lower row.  The contracted row-two coefficient `5` is an
incidence shadow, so the next independent row is row-zero coefficient
`5` (expanded `359`), taken together with the `gamma`-loaded I3
coefficient `3` (expanded `180`), whose literal content is extracted
here for the first time — the row-one packet only consumed it as an
abstract jet.  The `epsilon` load cancels through the constant I4 jet,
the `gamma` loads through the first-order I4 jet and the loaded I3
coefficient `3`, and the `i4` value through the rigid residual; the face,
discriminant, edge-cubic pin `4*b²*c₂ = 9*d₁²` and the three retained
jets absorb the homogeneous remainder.  Under the stored nonzeros the
row then pins the constant `c`-jet against the `gamma` load:
`2*c₁² = c₂*(8*c₀ + 21*gamma)`, dividing only by the stored nonzeros
`b` and `c₂`.  Every retained equation is re-emitted verbatim, the
row-two coefficient-`5` shadow is regenerated from the joined face, and
no sibling branch (pair-zero offset `180`, the offset-`120` small chart,
the aligned second-jet lane) is consumed.  The next unused rows are
row-zero coefficient `4` and the first `gamma`-loaded row-two
coefficient `4` (both expanded `299`), and the first `epsilon`-loaded I3
coefficient `2` (expanded `120`). -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryJoin68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Fourth coefficient of `A * A'` in the quartic chart. -/
theorem mul_derivative_coeff_four_ordinaryOneEightyJoin68
    (A : k[X]) (hA : A.natDegree ≤ 4) :
    (A * derivative A).coeff 4 =
      5 * A.coeff 4 * A.coeff 1 + 5 * A.coeff 2 * A.coeff 3 := by
  have hA5 : A.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have h := mul_coeff_four_oneTwentyOrdinaryNonzeroNext68 A (derivative A)
  norm_num [coeff_derivative, hA5] at h
  linear_combination h

/-- The `gamma`-loaded I3 coefficient `3` (expanded `180`) in
coordinates.  The row-one packet consumed it only as an abstract jet
against the row-one load; its literal content is extracted here. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_three_ordinaryOneEightyJoin68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff 3 =
      (8 / 9 : k) *
        (-(A.coeff 3 * B.coeff 0 * d.coeff 0) -
          A.coeff 2 * B.coeff 0 * d.coeff 1 +
          3 * c.coeff 0 * e.coeff 3 + 3 * c.coeff 1 * e.coeff 2 +
          3 * c.coeff 2 * e.coeff 1) := by
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hAB2 : (A * B).coeff 2 = A.coeff 2 * B.coeff 0 := by
    have h := coeff_mul_C A 2 (B.coeff 0)
    rw [← hBC] at h
    exact h
  have hAB3 : (A * B).coeff 3 = A.coeff 3 * B.coeff 0 := by
    have h := coeff_mul_C A 3 (B.coeff 0)
    rw [← hBC] at h
    exact h
  have hABd3 : (A * B * d).coeff 3 =
      A.coeff 2 * B.coeff 0 * d.coeff 1 +
        A.coeff 3 * B.coeff 0 * d.coeff 0 := by
    have h := mul_coeff_three_oneTwentyOrdinaryNonzero68 (A * B) d
    rw [hd2, hd3, hAB2, hAB3] at h
    linear_combination h
  have hce3 : (c * e).coeff 3 =
      c.coeff 0 * e.coeff 3 + c.coeff 1 * e.coeff 2 +
        c.coeff 2 * e.coeff 1 := by
    have h := mul_coeff_three_oneTwentyOrdinaryNonzero68 c e
    rw [hc3] at h
    linear_combination h
  have hB2c : (B ^ 2 * c).natDegree < 3 := by
    compute_degree
    omega
  have hdsq : (d ^ 2).natDegree < 3 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd3, hce3,
    coeff_eq_zero_of_natDegree_lt hB2c,
    coeff_eq_zero_of_natDegree_lt hdsq]
  ring

/-- Homogeneous row-zero coefficient `5` (expanded `359`).  The two
already-consumed I4 jets kill the two high coefficients of `B*e+c*d`;
the survivors pair the two `A*A'` jets with the low `B*e+c*d` jets, the
odd `A'`-jets with the `c²` core, and the loaded edge products. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_five_ordinaryOneEightyJoin68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (hface : B.coeff 0 * e.coeff 3 + c.coeff 2 * d.coeff 1 = 0)
    (hsecond : B.coeff 0 * e.coeff 2 +
      c.coeff 2 * d.coeff 0 + c.coeff 1 * d.coeff 1 = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 5 =
      (4 / 27 : k) *
        (-((6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) *
            (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0)) -
          5 * (A.coeff 4 * A.coeff 1 + A.coeff 2 * A.coeff 3) *
            (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
              c.coeff 0 * d.coeff 1) +
          2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 +
          6 * A.coeff 3 * B.coeff 0 * c.coeff 1 * c.coeff 2 +
          4 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 +
          8 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 -
          3 * (3 * A.coeff 3 * d.coeff 0 + 2 * A.coeff 2 * d.coeff 1) *
            e.coeff 3 -
          3 * (4 * A.coeff 4 * d.coeff 0 + 3 * A.coeff 3 * d.coeff 1) *
            e.coeff 2 -
          12 * A.coeff 4 * d.coeff 1 * e.coeff 1) := by
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
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hc4 : c.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hc5 : c.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have he5 : e.coeff 5 = 0 :=
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
  have hG5 := mul_derivative_coeff_five_oneTwentyOrdinaryNonzeroNext68 A hA
  have hG4 := mul_derivative_coeff_four_ordinaryOneEightyJoin68 A hA
  have hAAF : (A * derivative A * F).coeff 5 =
      (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) *
          (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
        5 * (A.coeff 4 * A.coeff 1 + A.coeff 2 * A.coeff 3) *
          (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
            c.coeff 0 * d.coeff 1) := by
    have h := mul_coeff_five_oneTwentyOrdinaryNonzeroNext68
      (A * derivative A) F
    rw [hF2, hF3, hF4, hF5, hG4, hG5, hF0, hF1] at h
    linear_combination h
  have hA'Bdeg : (derivative A * B).natDegree ≤ 3 := by
    compute_degree
    omega
  have hA'B4 : (derivative A * B).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
  have hA'B5 : (derivative A * B).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA'Bdeg.trans_lt (by norm_num))
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
  have hcsq5 : (c ^ 2).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hcsqdeg.trans_lt (by norm_num))
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
  have hBc2 : (derivative A * B * c ^ 2).coeff 5 =
      2 * A.coeff 2 * B.coeff 0 * c.coeff 2 ^ 2 +
        6 * A.coeff 3 * B.coeff 0 * c.coeff 1 * c.coeff 2 +
        4 * A.coeff 4 * B.coeff 0 * c.coeff 1 ^ 2 +
        8 * A.coeff 4 * B.coeff 0 * c.coeff 0 * c.coeff 2 := by
    have h := mul_coeff_five_oneTwentyOrdinaryNonzeroNext68
      (derivative A * B) (c ^ 2)
    rw [hcsq5, hA'B4, hA'B5, hA'B1, hA'B2, hA'B3, hcsq2, hcsq3, hcsq4] at h
    linear_combination h
  have hA'dDeg : (derivative A * d).natDegree ≤ 4 := by
    compute_degree
    omega
  have hA'd5 : (derivative A * d).coeff 5 = 0 :=
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
  have hA'd2 : (derivative A * d).coeff 2 =
      2 * A.coeff 2 * d.coeff 1 + 3 * A.coeff 3 * d.coeff 0 := by
    have h := mul_coeff_two68 (derivative A) d
    rw [hd2] at h
    norm_num [coeff_derivative] at h
    linear_combination h
  have hde : (derivative A * d * e).coeff 5 =
      (3 * A.coeff 3 * d.coeff 0 + 2 * A.coeff 2 * d.coeff 1) *
          e.coeff 3 +
        (4 * A.coeff 4 * d.coeff 0 + 3 * A.coeff 3 * d.coeff 1) *
          e.coeff 2 +
        4 * A.coeff 4 * d.coeff 1 * e.coeff 1 := by
    have h := mul_coeff_five_oneTwentyOrdinaryNonzeroNext68
      (derivative A * d) e
    rw [he4, he5, hA'd5, hA'd2, hA'd3, hA'd4] at h
    linear_combination h
  have hlow2 : (A * B ^ 2 * derivative d).natDegree < 5 := by
    compute_degree
    omega
  have hlow4 : (A * B * derivative B * d).natDegree < 5 := by
    rw [hderB, mul_zero, zero_mul, natDegree_zero]
    norm_num
  have hlow7 : (B * c * derivative e).natDegree < 5 := by
    compute_degree
    omega
  have hlow8 : (B * d * derivative d).natDegree < 5 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 5 := by
    rw [hderB, zero_mul, natDegree_zero]
    norm_num
  have hlow10 : (c * derivative c * d).natDegree < 5 := by
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
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- Exact literal load at the same coefficient: the `epsilon` load and
two of the `gamma` loads sit on the two `A*A'` jets, the remaining
`gamma` load on the discriminant edge `a*b*c₂`. -/
theorem cubicLoadRowZeroPolynomial68_coeff_five_ordinaryOneEightyJoin68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 =
      (8 / 9 : k) * gamma * A.coeff 4 * B.coeff 0 * c.coeff 2 -
        (2 / 3 : k) * epsilon * A.coeff 4 * A.coeff 2 * B.coeff 0 -
        (1 / 3 : k) * epsilon * A.coeff 3 ^ 2 * B.coeff 0 -
        (4 / 3 : k) * gamma * A.coeff 4 * A.coeff 2 * d.coeff 0 -
        (2 / 3 : k) * gamma * A.coeff 3 ^ 2 * d.coeff 0 -
        (10 / 9 : k) * gamma * A.coeff 4 * A.coeff 1 * d.coeff 1 -
        (10 / 9 : k) * gamma * A.coeff 2 * A.coeff 3 * d.coeff 1 := by
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
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hd5 : d.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hG5 := mul_derivative_coeff_five_oneTwentyOrdinaryNonzeroNext68 A hA
  have hG4 := mul_derivative_coeff_four_ordinaryOneEightyJoin68 A hA
  have hABA' : (A * B * derivative A).coeff 5 =
      (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) * B.coeff 0 := by
    have heq : A * B * derivative A =
        A * derivative A * C (B.coeff 0) := by
      conv_lhs => rw [hBC]
      ring
    rw [heq, coeff_mul_C, hG5]
  have hAAd : (A * derivative A * d).coeff 5 =
      (6 * A.coeff 4 * A.coeff 2 + 3 * A.coeff 3 ^ 2) * d.coeff 0 +
        5 * (A.coeff 4 * A.coeff 1 + A.coeff 2 * A.coeff 3) *
          d.coeff 1 := by
    have h := mul_coeff_five_oneTwentyOrdinaryNonzeroNext68
      (A * derivative A) d
    rw [hd2, hd3, hd4, hd5, hG4, hG5] at h
    linear_combination h
  have hBA'c : (B * derivative A * c).coeff 5 =
      4 * A.coeff 4 * B.coeff 0 * c.coeff 2 := by
    have heq : B * derivative A * c =
        derivative A * c * C (B.coeff 0) := by
      conv_lhs => rw [hBC]
      ring
    have h5 : (derivative A * c).coeff 5 =
        4 * A.coeff 4 * c.coeff 2 := by
      have h := coeff_mul_at_bounds68 (derivative A) c 3 2 hderA hc
      norm_num [coeff_derivative] at h
      linear_combination h
    rw [heq, coeff_mul_C, h5]
    ring
  have hlow2 : (B * derivative e).natDegree < 5 := by
    compute_degree
    omega
  have hlow5 : (d * derivative c).natDegree < 5 := by
    compute_degree
    omega
  have hlow6 : (d * derivative A).natDegree < 5 := by
    compute_degree
    omega
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 5 = _
  rw [hloadEq]
  simp only [coeff_smul, coeff_add, coeff_sub, smul_eq_mul, hABA', hAAd,
    hBA'c,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6]
  ring

/-- Scalar residual of the loaded row-zero coefficient `5` against the
joined frontier.  The `epsilon` load cancels through the constant I4
jet, the `gamma` loads through the first-order I4 jet and the loaded I3
coefficient `3`, and `i4` through the rigid residual; the face, the
discriminant, the edge-cubic pin `4*b²*c₂ = 9*d₁²` and the three
retained jets absorb the rest.  The row pins the constant `c`-jet
against the `gamma` load, dividing only by the stored nonzeros `b` and
`c₂`. -/
theorem fiveToSix_ordinaryOneEightyJoin_rowFive_residual68
    (a a₀ a₁ a₂ a₃ b c₀ c₁ c₂ d₀ d₁ e₀ e₁ e₂ e₃ gamma epsilon i4 : k)
    (hb : b ≠ 0) (hcTop : c₂ ≠ 0)
    (hface : b * e₃ + c₂ * d₁ = 0)
    (hdisc : a * b ^ 2 + 3 * c₂ ^ 2 = 0)
    (hedge : 9 * e₃ ^ 2 - 4 * c₂ ^ 3 = 0)
    (hsecond : b * e₂ + c₂ * d₀ + c₁ * d₁ = 0)
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
    (hrow : (4 / 27 : k) *
        (-((6 * a * a₂ + 3 * a₃ ^ 2) * (b * e₀ + c₀ * d₀)) -
          5 * (a * a₁ + a₂ * a₃) *
            (b * e₁ + c₁ * d₀ + c₀ * d₁) +
          2 * a₂ * b * c₂ ^ 2 + 6 * a₃ * b * c₁ * c₂ +
          4 * a * b * c₁ ^ 2 + 8 * a * b * c₀ * c₂ -
          3 * (3 * a₃ * d₀ + 2 * a₂ * d₁) * e₃ -
          3 * (4 * a * d₀ + 3 * a₃ * d₁) * e₂ -
          12 * a * d₁ * e₁) +
        ((8 / 9 : k) * gamma * a * b * c₂ -
          (2 / 3 : k) * epsilon * a * a₂ * b -
          (1 / 3 : k) * epsilon * a₃ ^ 2 * b -
          (4 / 3 : k) * gamma * a * a₂ * d₀ -
          (2 / 3 : k) * gamma * a₃ ^ 2 * d₀ -
          (10 / 9 : k) * gamma * a * a₁ * d₁ -
          (10 / 9 : k) * gamma * a₂ * a₃ * d₁) = 0) :
    2 * c₁ ^ 2 - c₂ * (8 * c₀ + 21 * gamma) = 0 := by
  have hpins : c₂ ^ 2 * (4 * b ^ 2 * c₂ - 9 * d₁ ^ 2) = 0 := by
    linear_combination (-(b ^ 2)) * hedge +
      (9 * (b * e₃ - c₂ * d₁)) * hface
  have hpin : 4 * b ^ 2 * c₂ - 9 * d₁ ^ 2 = 0 :=
    (mul_eq_zero.mp hpins).resolve_left (pow_ne_zero 2 hcTop)
  have hscaled : b ^ 4 * (c₂ ^ 6 *
      (2 * c₁ ^ 2 - c₂ * (8 * c₀ + 21 * gamma))) = 0 := by
    linear_combination
      ((81 * a * b ^ 5 * c₂ * d₁ ^ 2) / 32 : k) * hrow +
      ((18 * a₀ * a₃ * a * b ^ 5 * c₂ * d₁ ^ 2 + 108 * a₀ * a * b ^ 3 *
        c₁ * c₂ ^ 2 * d₁ ^ 2 + 18 * a₁ * a₂ * a * b ^ 5 * c₂ * d₁ ^ 2 -
        54 * a₁ * a * b ^ 4 * c₀ * c₂ * d₁ * e₃ - 81 * a₁ * a * b ^ 4 *
        c₂ * d₁ * e₃ * gamma + 54 * a₁ * a * b ^ 3 * c₀ * c₂ ^ 2 * d₁ ^ 2
        + 54 * a₁ * a * b ^ 3 * c₁ ^ 2 * c₂ * d₁ ^ 2 + 81 * a₁ * a * b ^
        3 * c₂ ^ 2 * d₁ ^ 2 * gamma - 36 * a ^ 2 * b ^ 6 * c₀ * c₂ * d₁ -
        54 * a ^ 2 * b ^ 6 * c₂ * d₁ * gamma - 36 * a * b ^ 4 * c₀ * c₂ ^
        3 * d₁ - 54 * a * b ^ 4 * c₂ ^ 3 * d₁ * gamma - 216 * a * b ^ 3 *
        c₀ * c₂ * d₁ ^ 2 * e₃ - 324 * a * b ^ 3 * c₂ * d₁ ^ 2 * e₃ *
        gamma + 432 * a * b ^ 2 * c₀ * c₂ ^ 2 * d₁ ^ 3 + 54 * a * b ^ 2 *
        c₁ ^ 2 * c₂ * d₁ ^ 3 + 648 * a * b ^ 2 * c₂ ^ 2 * d₁ ^ 3 * gamma
        - 1944 * c₁ ^ 2 * c₂ ^ 3 * d₁ ^ 3) / 16 : k) * hface +
      ((6 * a₀ * a ^ 2 * b ^ 5 * c₂ * d₁ ^ 2 + 6 * a₁ * a₃ * a * b ^ 5 *
        c₂ * d₁ ^ 2 + 3 * a₂ ^ 2 * a * b ^ 5 * c₂ * d₁ ^ 2) / 4 : k) *
        hsecond +
      ((90 * a₁ * a ^ 2 * b ^ 5 * c₂ * d₁ ^ 2 - 162 * a₁ * a * b ^ 4 * c₂
        ^ 2 * d₁ * e₃ - 162 * a₁ * a * b ^ 3 * c₂ ^ 3 * d₁ ^ 2 + 90 * a₂
        * a₃ * a * b ^ 5 * c₂ * d₁ ^ 2 - 108 * a ^ 2 * b ^ 6 * c₂ ^ 2 *
        d₁ + 216 * a ^ 2 * b ^ 4 * c₂ * d₁ ^ 3 - 108 * a * b ^ 4 * c₂ ^ 4
        * d₁ - 648 * a * b ^ 3 * c₂ ^ 2 * d₁ ^ 2 * e₃ + 324 * a * b ^ 2 *
        c₀ * c₁ * c₂ ^ 2 * d₁ * e₃ - 648 * a * b ^ 2 * c₀ * c₂ ^ 3 * d₀ *
        e₃ + 162 * a * b ^ 2 * c₁ * c₂ ^ 3 * d₁ * e₁ + 486 * a * b ^ 2 *
        c₁ * c₂ ^ 2 * d₁ * e₃ * gamma - 324 * a * b ^ 2 * c₂ ^ 4 * d₀ *
        e₁ - 972 * a * b ^ 2 * c₂ ^ 3 * d₀ * e₃ * gamma - 162 * a * b *
        c₀ * c₁ * c₂ ^ 3 * d₁ ^ 2 + 324 * a * b * c₀ * c₂ ^ 4 * d₀ * d₁ -
        486 * a * b * c₁ ^ 3 * c₂ ^ 2 * d₁ ^ 2 + 1458 * a * b * c₁ ^ 2 *
        c₂ ^ 3 * d₀ * d₁ - 972 * a * b * c₁ * c₂ ^ 4 * d₀ ^ 2 - 243 * a *
        b * c₁ * c₂ ^ 3 * d₁ ^ 2 * gamma + 486 * a * b * c₂ ^ 4 * d₀ * d₁
        * gamma) / 128 : k) * hfirst +
      ((54 * a₂ * a ^ 2 * b ^ 5 * c₂ * d₁ ^ 2 + 27 * a₃ ^ 2 * a * b ^ 5 *
        c₂ * d₁ ^ 2) / 64 : k) * hconstant +
      ((2 * a₂ * a * b ^ 5 * c₂ * d₁ ^ 2 + a₃ ^ 2 * b ^ 5 * c₂ * d₁ ^ 2)
        / 64 : k) * hrigid +
      ((81 * a₁ * a * b ^ 5 * c₂ * d₁ * e₃ + 81 * a₁ * a * b ^ 4 * c₂ ^ 2
        * d₁ ^ 2 + 54 * a₂ * a * b ^ 5 * c₂ * d₁ * e₂ + 54 * a₂ * a * b ^
        4 * c₁ * c₂ * d₁ ^ 2 + 54 * a₂ * a * b ^ 4 * c₂ ^ 2 * d₀ * d₁ -
        54 * a₃ * a * b ^ 5 * c₂ * d₀ * e₂ - 54 * a₃ * a * b ^ 4 * c₁ *
        c₂ * d₀ * d₁ - 54 * a₃ * a * b ^ 4 * c₂ ^ 2 * d₀ ^ 2 + 54 * a ^ 2
        * b ^ 7 * c₂ * d₁ + 54 * a * b ^ 5 * c₂ ^ 3 * d₁ + 162 * a * b ^
        4 * c₀ * c₂ * e₂ * e₃ + 162 * a * b ^ 4 * c₁ * c₂ * e₂ ^ 2 + 162
        * a * b ^ 4 * c₂ ^ 2 * e₁ * e₂ + 324 * a * b ^ 4 * c₂ * d₁ ^ 2 *
        e₃ + 243 * a * b ^ 4 * c₂ * e₂ * e₃ * gamma + 162 * a * b ^ 3 *
        c₀ * c₁ * c₂ * d₁ * e₃ + 162 * a * b ^ 3 * c₀ * c₂ ^ 2 * d₀ * e₃
        + 162 * a * b ^ 3 * c₁ ^ 2 * c₂ * d₁ * e₂ + 162 * a * b ^ 3 * c₁
        * c₂ ^ 2 * d₀ * e₂ + 162 * a * b ^ 3 * c₁ * c₂ ^ 2 * d₁ * e₁ +
        243 * a * b ^ 3 * c₁ * c₂ * d₁ * e₃ * gamma + 162 * a * b ^ 3 *
        c₂ ^ 3 * d₀ * e₁ + 243 * a * b ^ 3 * c₂ ^ 2 * d₀ * e₃ * gamma) /
        64 : k) * hJ3 +
      ((-9 * a₀ * a * b ^ 4 * c₂ * d₁ ^ 2 * e₃ - 9 * a₀ * a * b ^ 3 * c₂
        ^ 2 * d₁ ^ 3 + 9 * a₁ * a * b ^ 4 * c₂ * d₀ * d₁ * e₃ - 12 * a₁ *
        a * b ^ 4 * c₂ * d₁ ^ 2 * e₂ - 12 * a₁ * a * b ^ 3 * c₁ * c₂ * d₁
        ^ 3 - 3 * a₁ * a * b ^ 3 * c₂ ^ 2 * d₀ * d₁ ^ 2 - 3 * a₃ * a * b
        ^ 6 * c₂ * d₁ ^ 2 - 6 * a₃ * a * b ^ 4 * c₂ * d₀ ^ 2 * e₂ - 6 *
        a₃ * a * b ^ 3 * c₁ * c₂ * d₀ ^ 2 * d₁ - 6 * a₃ * a * b ^ 3 * c₂
        ^ 2 * d₀ ^ 3 - 27 * a₃ * b ^ 3 * c₂ * d₁ ^ 3 * e₃ + 6 * a ^ 2 * b
        ^ 6 * c₂ * d₀ * d₁ + 6 * a * b ^ 4 * c₂ ^ 3 * d₀ * d₁ + 36 * a *
        b ^ 3 * c₀ * c₂ * d₀ * e₂ * e₃ + 36 * a * b ^ 3 * c₁ * c₂ * d₀ *
        e₂ ^ 2 + 36 * a * b ^ 3 * c₂ ^ 2 * d₀ * e₁ * e₂ + 63 * a * b ^ 3
        * c₂ * d₀ * d₁ ^ 2 * e₃ + 54 * a * b ^ 3 * c₂ * d₀ * e₂ * e₃ *
        gamma + 27 * a * b ^ 3 * c₂ * d₁ ^ 3 * e₂ + 36 * a * b ^ 2 * c₀ *
        c₁ * c₂ * d₀ * d₁ * e₃ + 36 * a * b ^ 2 * c₀ * c₂ ^ 2 * d₀ ^ 2 *
        e₃ + 36 * a * b ^ 2 * c₁ ^ 2 * c₂ * d₀ * d₁ * e₂ + 72 * a * b ^ 2
        * c₁ * c₂ ^ 2 * d₀ ^ 2 * e₂ + 36 * a * b ^ 2 * c₁ * c₂ ^ 2 * d₀ *
        d₁ * e₁ + 54 * a * b ^ 2 * c₁ * c₂ * d₀ * d₁ * e₃ * gamma + 36 *
        a * b ^ 2 * c₂ ^ 3 * d₀ ^ 2 * e₁ + 54 * a * b ^ 2 * c₂ ^ 2 * d₀ ^
        2 * e₃ * gamma + 36 * a * b * c₁ ^ 2 * c₂ ^ 2 * d₀ ^ 2 * d₁ + 36
        * a * b * c₁ * c₂ ^ 3 * d₀ ^ 3 + 162 * b * c₁ * c₂ ^ 2 * d₁ ^ 3 *
        e₃) / 8 : k) * hT1 +
      ((-24 * a₀ * a ^ 2 * b ^ 5 * c₂ * d₁ ^ 2 - 54 * a₁ * a * b ^ 4 * c₁
        * c₂ * d₁ * e₃ + 90 * a₁ * a * b ^ 3 * c₁ * c₂ ^ 2 * d₁ ^ 2 - 36
        * a ^ 2 * b ^ 6 * c₁ * c₂ * d₁ + 72 * a ^ 2 * b ^ 4 * c₂ * d₀ *
        d₁ ^ 2 - 36 * a * b ^ 4 * c₁ * c₂ ^ 3 * d₁ - 108 * a * b ^ 3 * c₀
        ^ 2 * c₂ * e₃ ^ 2 - 216 * a * b ^ 3 * c₀ * c₁ * c₂ * e₂ * e₃ -
        216 * a * b ^ 3 * c₀ * c₂ ^ 2 * e₁ * e₃ - 324 * a * b ^ 3 * c₀ *
        c₂ * e₃ ^ 2 * gamma - 108 * a * b ^ 3 * c₁ ^ 2 * c₂ * e₂ ^ 2 -
        216 * a * b ^ 3 * c₁ * c₂ ^ 2 * e₁ * e₂ - 216 * a * b ^ 3 * c₁ *
        c₂ * d₁ ^ 2 * e₃ - 324 * a * b ^ 3 * c₁ * c₂ * e₂ * e₃ * gamma -
        108 * a * b ^ 3 * c₂ ^ 3 * e₁ ^ 2 - 324 * a * b ^ 3 * c₂ ^ 2 * e₁
        * e₃ * gamma - 243 * a * b ^ 3 * c₂ * e₃ ^ 2 * gamma ^ 2 + 108 *
        a * b ^ 2 * c₀ * c₁ ^ 2 * c₂ * d₁ * e₃ - 648 * a * b ^ 2 * c₀ *
        c₁ * c₂ ^ 2 * d₀ * e₃ + 54 * a * b ^ 2 * c₁ ^ 3 * c₂ * d₁ * e₂ -
        540 * a * b ^ 2 * c₁ ^ 2 * c₂ ^ 2 * d₀ * e₂ + 108 * a * b ^ 2 *
        c₁ ^ 2 * c₂ ^ 2 * d₁ * e₁ + 162 * a * b ^ 2 * c₁ ^ 2 * c₂ * d₁ *
        e₃ * gamma - 648 * a * b ^ 2 * c₁ * c₂ ^ 3 * d₀ * e₁ - 972 * a *
        b ^ 2 * c₁ * c₂ ^ 2 * d₀ * e₃ * gamma - 324 * a * b ^ 2 * c₁ * c₂
        ^ 2 * d₁ ^ 3 - 81 * a * b * c₁ ^ 4 * c₂ * d₁ ^ 2 + 378 * a * b *
        c₁ ^ 3 * c₂ ^ 2 * d₀ * d₁ - 864 * a * b * c₁ ^ 2 * c₂ ^ 3 * d₀ ^
        2) / 32 : k) * hT3 +
      ((-24 * a₀ * a ^ 2 * b ^ 5 * c₂ * d₁ ^ 2 - 54 * a₁ * a * b ^ 4 * c₁
        * c₂ * d₁ * e₃ + 90 * a₁ * a * b ^ 3 * c₁ * c₂ ^ 2 * d₁ ^ 2 - 36
        * a ^ 2 * b ^ 6 * c₁ * c₂ * d₁ - 180 * a ^ 2 * b ^ 4 * c₁ * d₁ ^
        3 - 36 * a * b ^ 4 * c₁ * c₂ ^ 3 * d₁ - 108 * a * b ^ 3 * c₀ ^ 2
        * c₂ * e₃ ^ 2 - 324 * a * b ^ 3 * c₀ * c₂ * e₃ ^ 2 * gamma - 540
        * a * b ^ 3 * c₁ * c₂ * d₁ ^ 2 * e₃ - 243 * a * b ^ 3 * c₂ * e₃ ^
        2 * gamma ^ 2 + 216 * a * b ^ 2 * c₀ ^ 2 * c₂ ^ 2 * d₁ * e₃ + 324
        * a * b ^ 2 * c₀ * c₁ ^ 2 * c₂ * d₁ * e₃ - 216 * a * b ^ 2 * c₀ *
        c₁ * c₂ ^ 2 * d₀ * e₃ + 648 * a * b ^ 2 * c₀ * c₂ ^ 2 * d₁ * e₃ *
        gamma + 486 * a * b ^ 2 * c₁ ^ 2 * c₂ * d₁ * e₃ * gamma - 324 * a
        * b ^ 2 * c₁ * c₂ ^ 2 * d₀ * e₃ * gamma + 486 * a * b ^ 2 * c₂ ^
        2 * d₁ * e₃ * gamma ^ 2 - 108 * a * b * c₀ ^ 2 * c₂ ^ 3 * d₁ ^ 2
        - 324 * a * b * c₀ * c₁ ^ 2 * c₂ ^ 2 * d₁ ^ 2 + 216 * a * b * c₀
        * c₁ * c₂ ^ 3 * d₀ * d₁ - 324 * a * b * c₀ * c₂ ^ 3 * d₁ ^ 2 *
        gamma - 243 * a * b * c₁ ^ 4 * c₂ * d₁ ^ 2 + 324 * a * b * c₁ ^ 3
        * c₂ ^ 2 * d₀ * d₁ - 108 * a * b * c₁ ^ 2 * c₂ ^ 3 * d₀ ^ 2 - 486
        * a * b * c₁ ^ 2 * c₂ ^ 2 * d₁ ^ 2 * gamma + 324 * a * b * c₁ *
        c₂ ^ 3 * d₀ * d₁ * gamma - 243 * a * b * c₂ ^ 3 * d₁ ^ 2 * gamma
        ^ 2) / 32 : k) * hT2 +
      ((12 * a * b ^ 4 * c₀ * c₂ ^ 2 * d₁ ^ 2 + 6 * a * b ^ 4 * c₁ ^ 2 *
        c₂ * d₁ ^ 2 + 36 * a * b ^ 4 * c₂ ^ 2 * d₁ ^ 2 * gamma - 36 * a *
        b ^ 2 * c₀ * c₂ * d₁ ^ 4 - 45 * a * b ^ 2 * c₁ ^ 2 * d₁ ^ 4 - 54
        * a * b ^ 2 * c₂ * d₁ ^ 4 * gamma - 54 * b ^ 2 * c₂ ^ 4 * d₁ ^ 2
        * gamma - 108 * c₀ * c₂ ^ 3 * d₁ ^ 4 + 351 * c₁ ^ 2 * c₂ ^ 2 * d₁
        ^ 4 - 162 * c₂ ^ 3 * d₁ ^ 4 * gamma) / 8 : k) * hdisc +
      ((-16 * b ^ 2 * c₀ * c₂ ^ 6 + 4 * b ^ 2 * c₁ ^ 2 * c₂ ^ 5 - 42 * b
        ^ 2 * c₂ ^ 6 * gamma - 36 * c₀ * c₂ ^ 5 * d₁ ^ 2 + 9 * c₁ ^ 2 *
        c₂ ^ 4 * d₁ ^ 2 - 54 * c₂ ^ 5 * d₁ ^ 2 * gamma) / 8 : k) * hpin
  have h1 := (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 4 hb)
  exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 6 hcTop)

set_option maxHeartbeats 15000000 in
/-- Joined source packet at ordinary offset `180`.  Both imported
frontiers are merged over the common source variables: the rigid I4
residual, the edge cubic, the exact constant-I3 identity and the three
first jets are retained verbatim, the literal source row-zero
coefficient `5` (expanded `359`) is consumed together with the loaded
I3 coefficient `3` (expanded `180`), and the row-two coefficient-`5`
incidence shadow is regenerated from the joined face.  The new gain
pins the constant `c`-jet against the `gamma` load.  No sibling branch
is consumed and no stored nonzero is weakened. -/
theorem fiveToSix_offsetOneEighty_ordinaryJoin_source_packet68
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
          A B C0 D0 E0) D0 E0).coeff 5 = 0) :
    (27 * A.coeff 4 * i4 + 32 * A.coeff 4 * B.coeff 0 ^ 3 +
        216 * d.coeff 1 * e.coeff 3 = 0) ∧
      (9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0) ∧
      (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) ∧
      (A.coeff 3 * B.coeff 0 ^ 2 + 6 * c.coeff 1 * c.coeff 2 = 0) ∧
      (2 * c.coeff 2 * d.coeff 0 - c.coeff 1 * d.coeff 1 = 0) ∧
      (2 * B.coeff 0 * e.coeff 2 + 3 * c.coeff 1 * d.coeff 1 = 0) ∧
      (2 * c.coeff 1 ^ 2 -
        c.coeff 2 * (8 * c.coeff 0 + 21 * gamma) = 0) ∧
      ((lowerRowTwoPolynomial68
          (integratedSPolynomial68 0 alpha 0 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d))
          (integratedTPolynomial68 0 alpha 0 gamma epsilon A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
          (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
          (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
          B ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff 5 =
        0) := by
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
  let C0 : k[X] := (1 / 3 : k) • A ^ 2 + c
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change (lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B C0 D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B C0 D0 E0) D0 E0).coeff 5 = 0 at hrowZero
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon 0 eta A B c D0 e
  have hhom : cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
      secondaryResidualRowZeroPolynomial68 A B c d e := by
    simpa only [D0] using
      cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e
  have hres5 :=
    secondaryResidualRowZeroPolynomial68_coeff_five_ordinaryOneEightyJoin68
      A B c d e hA hB hc hd he hface hsecond
  have hload5 := cubicLoadRowZeroPolynomial68_coeff_five_ordinaryOneEightyJoin68
    alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add, hhom, hres5, hload5] at hrowZero
  have hgain := fiveToSix_ordinaryOneEightyJoin_rowFive_residual68
    (A.coeff 4) (A.coeff 0) (A.coeff 1) (A.coeff 2) (A.coeff 3)
    (B.coeff 0) (c.coeff 0) (c.coeff 1) (c.coeff 2)
    (d.coeff 0) (d.coeff 1)
    (e.coeff 0) (e.coeff 1) (e.coeff 2) (e.coeff 3)
    gamma epsilon i4 hb hcTop hface hdisc hedge hsecond hfirst
    hconstant hi4rigid hjetDisc hjetEdge hjetLoad hJ3s
    (by linear_combination hrowZero)
  refine ⟨hi4rigid, hedge, hi3, hjetDisc, hjetEdge, hjetLoad, hgain, ?_⟩
  rw [fiveToSix_offsetOneEighty_rowTwo_coeff_five_incidence68
      alpha gamma epsilon eta A B c d e hA hB hc hd he, hface, mul_zero]

#print axioms mul_derivative_coeff_four_ordinaryOneEightyJoin68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_three_ordinaryOneEightyJoin68
#print axioms secondaryResidualRowZeroPolynomial68_coeff_five_ordinaryOneEightyJoin68
#print axioms cubicLoadRowZeroPolynomial68_coeff_five_ordinaryOneEightyJoin68
#print axioms fiveToSix_ordinaryOneEightyJoin_rowFive_residual68
#print axioms fiveToSix_offsetOneEighty_ordinaryJoin_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryJoin68

end Max11DegreeRoutes
