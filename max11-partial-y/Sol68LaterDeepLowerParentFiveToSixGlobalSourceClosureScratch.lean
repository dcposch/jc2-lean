import Sol68LaterDeepLowerParentFiveToSixPositiveCoefficientSelectorScratch

/-! # Terminal-safe closure of the final OffsetNinety inventory

The aligned nonzero packet is the already closed `(N,G)=(2,6)` chart.  The
only new leaf is the exact-six `B=0`, `c₂≠0` chart.  Its short coefficient
cascade below uses only positive row-zero coefficients; coefficient zero
continues to equal the nonzero terminal constant.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixGlobalSourceClosure68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem fiveToSix_cOnly_i4_coeff_four68
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (hB0 : B = 0) (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 4 =
      (8 / 3 : k) * c.coeff 2 * d.coeff 2 + zeta * A.coeff 4 := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hB0]
  have hcd := coeff_mul_at_bounds68 c d 2 2 hc hd
  norm_num at hcd
  have hd4 : d.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hz4 : (0 : k[X]).coeff 4 = 0 := by simp
  simp only [secondaryResidualInvariantFourPolynomial68, zero_pow,
    smul_zero, zero_mul, zero_add, coeff_add, coeff_smul, smul_eq_mul,
    hz4, hcd, hd4, mul_zero, add_zero]
  norm_num
  ring

theorem fiveToSix_cOnly_i3_coeff_six68
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (hB0 : B = 0) (hc : c.natDegree ≤ 2)
    (hd : d.natDegree ≤ 2) (he : e.natDegree ≤ 4) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 =
      (8 / 3 : k) * c.coeff 2 * e.coeff 4 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    hB0]
  have hce := coeff_mul_at_bounds68 c e 2 4 hc he
  norm_num at hce
  have hd2 : (d ^ 2).natDegree < 6 := by compute_degree; omega
  have hc6 : c.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he6 : e.coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hz6 : (0 : k[X]).coeff 6 = 0 := by simp
  simp only [secondaryResidualInvariantThreePolynomial68, zero_mul,
    zero_pow, smul_zero, zero_add, coeff_sub, coeff_add, coeff_smul,
    smul_eq_mul, hz6, hce, coeff_eq_zero_of_natDegree_lt hd2, hc6, he6,
    mul_zero, add_zero, sub_zero]
  norm_num
  ring

theorem fiveToSix_alignedSmall_i4_coeff_five68
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 =
      (8 / 3 : k) *
        (B.coeff 0 * e.coeff 5 + c.coeff 2 * d.coeff 3) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
  have hBe := coeff_mul_at_bounds68 B e 0 5 hB he
  have hcd := coeff_mul_at_bounds68 c d 2 3 hc hd
  norm_num at hBe hcd
  have hB3 : (B ^ 3).natDegree < 5 := by compute_degree; omega
  have hA5 : A.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hB5 : B.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hd5 : d.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3,
    hBe, hcd, hA5, hB5, hd5, mul_zero, add_zero]
  ring

theorem fiveToSix_cOnly_rowOne_coeff_eight68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hB0 : B = 0) (hA : A.natDegree ≤ 4)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 8 =
      (40 / 9 : k) * A.coeff 4 * c.coeff 2 * e.coeff 3 := by
  have h1 := coeff_mul_mul_derivative_at_bounds68 A c e 4 2 3
    (by norm_num) hA hc he
  norm_num at h1
  have h2raw := coeff_mul_mul_derivative_at_bounds68 A e c 4 3 2
    (by norm_num) hA he hc
  norm_num at h2raw
  have h2 : (A * derivative c * e).coeff 8 =
      2 * A.coeff 4 * c.coeff 2 * e.coeff 3 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have hlow1 : (derivative A * d ^ 2).natDegree < 8 := by
    compute_degree; omega
  have hlow2 : (c ^ 2 * derivative c).natDegree < 8 := by
    compute_degree; omega
  have hlow3 : (e * derivative e).natDegree < 8 := by
    compute_degree; omega
  have hz8 : (0 : k[X]).coeff 8 = 0 := by simp
  have hres : (secondaryResidualRowOnePolynomial68 A B c d e).coeff 8 =
      (40 / 9 : k) * A.coeff 4 * c.coeff 2 * e.coeff 3 := by
    rw [hB0]
    simp only [secondaryResidualRowOnePolynomial68, zero_mul, mul_zero,
      zero_pow, derivative_zero, smul_zero, zero_add, sub_zero,
      coeff_smul, coeff_add, coeff_sub, hz8, smul_eq_mul, h1, h2,
      coeff_eq_zero_of_natDegree_lt hlow1,
      coeff_eq_zero_of_natDegree_lt hlow2,
      coeff_eq_zero_of_natDegree_lt hlow3]
    norm_num
    ring
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let Ur : k[X] := (2 / 3 * gamma : k) • B
  have hloadEq :
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c D0 e =
      Ur * derivative D0 +
        (4 / 3 * gamma : k) • (A * derivative e - c * derivative c) +
        (2 / 3 * epsilon : k) • (A * derivative c) +
        (2 * epsilon : k) • derivative e -
        (2 / 3 * gamma : k) • (D0 * derivative B) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
      cubicLoadUPolynomial68, cubicLoadVPolynomial68, D0, Ur,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hload : (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 8 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hloadEq]
    simp only [Ur, D0, hB0, smul_zero, zero_add, mul_zero,
      derivative_zero, zero_mul]
    compute_degree
    omega
  rw [coeff_add, hres]
  change _ + (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
    A B c D0 e).coeff 8 = _
  rw [hload, add_zero]

theorem fiveToSix_cOnly_rowTwo_coeff_six68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hB0 : B = 0) (hA : A.natDegree ≤ 4)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 =
      (8 / 9 : k) * A.coeff 4 * c.coeff 2 * d.coeff 1 := by
  have h1 := coeff_mul_mul_derivative_at_bounds68 A c d 4 2 1
    (by norm_num) hA hc hd
  norm_num at h1
  have h2raw := coeff_mul_mul_derivative_at_bounds68 A d c 4 1 2
    (by norm_num) hA hd hc
  norm_num at h2raw
  have h2 : (A * derivative c * d).coeff 6 =
      2 * A.coeff 4 * c.coeff 2 * d.coeff 1 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have h3 := coeff_mul_mul_derivative_at_bounds68 c d A 2 1 4
    (by norm_num) hc hd hA
  norm_num at h3
  have h3' : (derivative A * c * d).coeff 6 =
      4 * A.coeff 4 * c.coeff 2 * d.coeff 1 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (d * derivative e).natDegree < 6 := by compute_degree; omega
  have hlow2 : (derivative d * e).natDegree < 6 := by compute_degree; omega
  have hz6 : (0 : k[X]).coeff 6 = 0 := by simp
  have hres : (secondaryResidualRowTwoPolynomial68 A B c d e).coeff 6 =
      (8 / 9 : k) * A.coeff 4 * c.coeff 2 * d.coeff 1 := by
    rw [hB0]
    simp only [secondaryResidualRowTwoPolynomial68, zero_mul, mul_zero,
      zero_pow, derivative_zero, smul_zero, zero_add, sub_zero,
      coeff_smul, coeff_add, coeff_sub, hz6, smul_eq_mul, h1, h2, h3',
      coeff_eq_zero_of_natDegree_lt hlow1,
      coeff_eq_zero_of_natDegree_lt hlow2]
    norm_num
    ring
  have hload6 : (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 = 0 := by
    -- The proof of the predecessor coefficient identifies a degree-`≤4`
    -- load; at coefficient six only that degree fact is needed.
    let D0 : k[X] := (1 / 3 : k) • (A * B) + d
    have hloadEq :
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c D0 e =
        (4 / 3 * gamma : k) • (A * derivative d) -
          (2 / 3 * gamma : k) • (derivative A * d) -
          (4 / 3 * gamma : k) • (B * derivative c) -
          (4 / 3 * gamma : k) • (c * derivative B) -
          (1 / 3 * epsilon : k) • (derivative A * B) +
          (2 / 3 * epsilon : k) • (A * derivative B) +
          (2 * epsilon : k) • derivative d := by
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
        cubicLoadTPolynomial68, cubicLoadUPolynomial68,
        cubicLoadVPolynomial68, D0,
        zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
        derivative_add, derivative_sub, derivative_mul, derivative_pow,
        derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
        map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
        RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
      ring
    change (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 6 = 0
    apply coeff_eq_zero_of_natDegree_lt
    rw [hloadEq]
    simp only [D0, hB0, smul_zero, zero_add, mul_zero,
      derivative_zero, zero_mul]
    compute_degree
    omega
  rw [coeff_add, hres, hload6, add_zero]

theorem fiveToSix_cOnly_i4_coeff_two68
    (gamma epsilon : k) (A B c d e : k[X])
    (hB0 : B = 0) (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 0) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 2 =
      (8 / 3 : k) * c.coeff 2 * d.coeff 0 := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hB0]
  have hcd := coeff_mul_at_bounds68 c d 2 0 hc hd
  norm_num at hcd
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have hz2 : (0 : k[X]).coeff 2 = 0 := by simp
  simp only [secondaryResidualInvariantFourPolynomial68, zero_pow,
    smul_zero, zero_mul, zero_add, coeff_add, coeff_smul, smul_eq_mul,
    hz2, hcd, hd2, mul_zero, add_zero]
  norm_num
  ring

theorem fiveToSix_cOnly_i3_coeff_four68
    (gamma epsilon : k) (A B c d e : k[X])
    (hB0 : B = 0) (hd0 : d = 0)
    (hc : c.natDegree ≤ 2) (he : e.natDegree ≤ 2) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 4 =
      (8 / 3 : k) * c.coeff 2 * e.coeff 2 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    hB0, hd0]
  have hce := coeff_mul_at_bounds68 c e 2 2 hc he
  norm_num at hce
  have hc4 : c.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hz4 : (0 : k[X]).coeff 4 = 0 := by simp
  simp only [secondaryResidualInvariantThreePolynomial68, zero_mul,
    zero_pow, smul_zero, zero_add, coeff_sub, coeff_add, coeff_smul,
    smul_eq_mul, hz4, hce, hc4, he4, mul_zero, add_zero, sub_zero]
  norm_num
  ring

theorem fiveToSix_cOnly_i3_coeff_three68
    (gamma epsilon : k) (A B c d e : k[X])
    (hB0 : B = 0) (hd0 : d = 0)
    (hc : c.natDegree ≤ 2) (he : e.natDegree ≤ 1) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 =
      (8 / 3 : k) * c.coeff 2 * e.coeff 1 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    hB0, hd0]
  have hce := coeff_mul_at_bounds68 c e 2 1 hc he
  norm_num at hce
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have he3 : e.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hz3 : (0 : k[X]).coeff 3 = 0 := by simp
  simp only [secondaryResidualInvariantThreePolynomial68, zero_mul,
    zero_pow, smul_zero, zero_add, coeff_sub, coeff_add, coeff_smul,
    smul_eq_mul, hz3, hce, hc3, he3, mul_zero, add_zero, sub_zero]
  norm_num
  ring

theorem fiveToSix_cOnly_i3_coeff_two68
    (gamma epsilon : k) (A B c d e : k[X])
    (hB0 : B = 0) (hd0 : d = 0)
    (hc : c.natDegree ≤ 2) (he : e.natDegree ≤ 0) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 2 =
      (8 / 3 : k) * c.coeff 2 * e.coeff 0 +
        2 * epsilon * c.coeff 2 := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    hB0, hd0]
  have hce := coeff_mul_at_bounds68 c e 2 0 hc he
  norm_num at hce
  have he2 : e.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hz2 : (0 : k[X]).coeff 2 = 0 := by simp
  simp only [secondaryResidualInvariantThreePolynomial68, zero_mul,
    zero_pow, smul_zero, zero_add, coeff_sub, coeff_add, coeff_smul,
    smul_eq_mul, hz2, hce, he2, mul_zero, add_zero, sub_zero]
  norm_num
  ring

set_option maxHeartbeats 30000000 in
theorem fiveToSix_exactSix_cOnly_positive_source_false68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB0 : B = 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4)
    (ha : A.coeff 4 ≠ 0) (hc2 : c.coeff 2 ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow0pos : ∀ j, 0 < j →
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) : False := by
  have hB : B.natDegree ≤ 0 := by rw [hB0]; norm_num
  have hd3 : d.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have he4 : e.coeff 4 = 0 := by
    have hcoeff := congrArg (fun p : k[X] => p.coeff 6) hi3
    rw [fiveToSix_cOnly_i3_coeff_six68 gamma epsilon zeta A B c d e
      hB0 hc hd he] at hcoeff
    norm_num [coeff_C] at hcoeff
    rcases hcoeff with hc0 | he0
    · exact False.elim (hc2 hc0)
    · exact he0
  have he5 : e.coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hi4four := congrArg (fun p : k[X] => p.coeff 4) hi4
  rw [fiveToSix_cOnly_i4_coeff_four68 gamma epsilon zeta A B c d e
    hB0 hc hd] at hi4four
  norm_num [coeff_C] at hi4four
  have hrow11 := hrow0pos 11 (by norm_num)
  rw [coeff_add,
    secondaryResidualRowZeroPolynomial68_coeff_eleven_smallChart68
      A B c d e hA hB hc (hd.trans (by norm_num))
        (he.trans (by norm_num)),
    cubicLoadRowZeroPolynomial68_coeff_eleven_smallChart68
      alpha gamma epsilon zeta eta A B c d e hA hB hc
        (hd.trans (by norm_num)) (he.trans (by norm_num))] at hrow11
  simp only [hB0, coeff_zero, zero_mul, hd3, he4, he5, mul_zero,
    zero_add, add_zero] at hrow11
  have hzetaScaled : (2 / 3 : k) * zeta * A.coeff 4 ^ 3 = 0 := by
    linear_combination hrow11 + (2 / 9 : k) * A.coeff 4 ^ 2 * hi4four
  have hzetaCube : zeta * A.coeff 4 ^ 3 = 0 := by
    linear_combination (3 / 2 : k) * hzetaScaled
  have hzeta : zeta = 0 :=
    (mul_eq_zero.mp hzetaCube).resolve_right (pow_ne_zero 3 ha)
  have hd2 : d.coeff 2 = 0 := by
    rw [hzeta, zero_mul, add_zero] at hi4four
    exact (mul_eq_zero.mp hi4four).resolve_left
      (mul_ne_zero (by norm_num) hc2)
  have hd1deg : d.natDegree ≤ 1 := natDegree_le_pred hd hd2
  have he3deg : e.natDegree ≤ 3 := natDegree_le_pred he he4
  have hrow1z := hrow1
  have hrow2z := hrow2
  rw [hzeta] at hrow1z hrow2z
  have hrow8 := congrArg (fun p : k[X] => p.coeff 8) hrow1z
  rw [fiveToSix_cOnly_rowOne_coeff_eight68 alpha gamma epsilon eta
    A B c d e hB0 hA hc hd1deg he3deg] at hrow8
  simp only [coeff_zero] at hrow8
  have he3 : e.coeff 3 = 0 :=
    (mul_eq_zero.mp hrow8).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) ha) hc2)
  have he2deg : e.natDegree ≤ 2 := natDegree_le_pred he3deg he3
  have hrow6 := congrArg (fun p : k[X] => p.coeff 6) hrow2z
  rw [fiveToSix_cOnly_rowTwo_coeff_six68 alpha gamma epsilon eta
    A B c d e hB0 hA hc hd1deg he3deg] at hrow6
  simp only [coeff_zero] at hrow6
  have hd1 : d.coeff 1 = 0 :=
    (mul_eq_zero.mp hrow6).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) ha) hc2)
  have hd0deg : d.natDegree ≤ 0 := natDegree_le_pred hd1deg hd1
  have hi4z := hi4
  rw [hzeta] at hi4z
  have hi4two := congrArg (fun p : k[X] => p.coeff 2) hi4z
  rw [fiveToSix_cOnly_i4_coeff_two68 gamma epsilon A B c d e
    hB0 hc hd0deg] at hi4two
  norm_num [coeff_C] at hi4two
  have hd0 : d.coeff 0 = 0 :=
    hi4two.resolve_left hc2
  have hdpoly : d = 0 := by
    rw [eq_C_of_natDegree_le_zero hd0deg, hd0]
    simp
  have hi3z := hi3
  rw [hzeta] at hi3z
  have hi3four := congrArg (fun p : k[X] => p.coeff 4) hi3z
  rw [fiveToSix_cOnly_i3_coeff_four68 gamma epsilon A B c d e
    hB0 hdpoly hc he2deg] at hi3four
  norm_num [coeff_C] at hi3four
  have he2 : e.coeff 2 = 0 :=
    hi3four.resolve_left hc2
  have he1deg : e.natDegree ≤ 1 := natDegree_le_pred he2deg he2
  have hi3three := congrArg (fun p : k[X] => p.coeff 3) hi3z
  rw [fiveToSix_cOnly_i3_coeff_three68 gamma epsilon A B c d e
    hB0 hdpoly hc he1deg] at hi3three
  norm_num [coeff_C] at hi3three
  have he1 : e.coeff 1 = 0 :=
    hi3three.resolve_left hc2
  have he0deg : e.natDegree ≤ 0 := natDegree_le_pred he1deg he1
  have hi3two := congrArg (fun p : k[X] => p.coeff 2) hi3z
  rw [fiveToSix_cOnly_i3_coeff_two68 gamma epsilon A B c d e
    hB0 hdpoly hc he0deg] at hi3two
  norm_num [coeff_C] at hi3two
  have hepsilon : 4 * e.coeff 0 + 3 * epsilon = 0 := by
    have hfac : c.coeff 2 * (4 * e.coeff 0 + 3 * epsilon) = 0 := by
      linear_combination (3 / 2 : k) * hi3two
    exact (mul_eq_zero.mp hfac).resolve_left hc2
  have hrow5 := congrArg (fun p : k[X] => p.coeff 5) hrow1z
  rw [fiveToSix_pairZero_rowOne_coeff_five68 alpha gamma epsilon eta
    A B c d e hA hB hc hdpoly he0deg] at hrow5
  simp only [coeff_zero, hB0, zero_pow, zero_mul, zero_add] at hrow5
  have hcubic : (-16 / 9 : k) * c.coeff 2 ^ 3 = 0 := by
    linear_combination hrow5 - (4 / 9 : k) * A.coeff 4 * c.coeff 2 * hepsilon
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hc2)) hcubic

set_option maxHeartbeats 30000000 in
/-- Full source contradiction on the exact ordinary `(n,g)=(120,360)`
wall.  The terminal RHS is used only through its positive-coefficient
adapter: the nonzero coefficient at zero is retained throughout. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_offsetOneTwenty_source_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlater :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 120 ∧ g = 360) : False := by
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
  let cu := cubicCDefectPolynomial68 A C0
  let du := secondaryDDefectPolynomial68 A B D
  let eu := cubicEDefectPolynomial68 A C0 E
  change 3 * n ≤ 2 * g at hlater
  change n = 120 ∧ g = 360 at hwall
  have hred :=
    maximalExpandedIntegratedPolynomialLowerSystem_offsetOneTwenty_ordinary_positive_reduction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change Be.coeff (3 * n - g) = 0 ∨
    (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) at hred
  have hp :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinety_with_terminalRHS68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (((_ ∧ _ ∧ _) ∨ _) ∧
      ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∨
        (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))) ∧ _ at hp
  rcases hp with ⟨hoffset, hadapter⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hparent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60 at hparent
  have hcexpand : ce = expand k 60 cu := by
    simpa only [ce, Ae, Ce, cu] using
      expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 du := by
    simpa only [d, Ae, Be, De, du] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 eu := by
    simpa only [ee, Ae, Ce, Ee, eu] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hA4 : A.natDegree ≤ 4 := by
    have h := data.hA
    simp only [Ae, natDegree_expand, hwall.1] at h
    omega
  have hB0deg : B.natDegree ≤ 0 := by
    have h := data.hB
    simp only [Be, natDegree_expand, hwall.1, hwall.2] at h
    omega
  have hc2deg : cu.natDegree ≤ 2 := by
    have h := data.hc
    rw [hcexpand, natDegree_expand, hwall.1, hwall.2] at h
    omega
  have hd3deg : du.natDegree ≤ 3 := by
    have h := hparent.2.2.2.2.2.2.2.2.1
    have h' : (expand k 60 du).natDegree ≤ 5 * n - g - 60 := by
      rw [← hdexpand]
      exact h
    rw [natDegree_expand, hwall.1, hwall.2] at h'
    omega
  have he5deg : eu.natDegree ≤ 5 := by
    have h := hparent.2.2.2.2.2.2.2.2.2
    have h' : (expand k 60 eu).natDegree ≤ 6 * n - g - 60 := by
      rw [← heexpand]
      exact h
    rw [natDegree_expand, hwall.1, hwall.2] at h'
    omega
  have ha4 : A.coeff 4 ≠ 0 := by
    have h := data.ha
    simpa [Ae, hwall.1, coeff_expand] using h
  change FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta
    terminal A B cu du eu at hadapter
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, hrow1, hrow2, hrow0pos, _hiff⟩
  rcases hred with hbzero | hnz
  · have hzero := hoffset.2.resolve_right (by
      intro hn
      have hb := hn.2.2.1
      change Be.coeff (3 * n - g) ≠ 0 at hb
      exact hb hbzero)
    have hb0 : B.coeff 0 = 0 := by
      simpa [Be, hwall.1, hwall.2, coeff_expand] using hbzero
    have hBpoly : B = 0 := by
      rw [eq_C_of_natDegree_le_zero hB0deg, hb0]
      simp
    have hctop :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (show 5 * n < 2 * g ∧ 2 * g ≤ 6 * n by omega))
    change Be.coeff (3 * n - g) ≠ 0 ∨
      ce.coeff (4 * n - g) ≠ 0 at hctop
    have hcTopE : ce.coeff (4 * n - g) ≠ 0 :=
      hctop.resolve_left (fun h => h hbzero)
    have hcTop : cu.coeff 2 ≠ 0 := by
      simpa [hwall.1, hwall.2, hcexpand, coeff_expand] using hcTopE
    have hd2deg : du.natDegree ≤ 2 := by
      have h := hzero.2.2.1
      have h' : (expand k 60 du).natDegree ≤ 5 * n - g - 120 := by
        rw [← hdexpand]
        exact h
      rw [natDegree_expand, hwall.1, hwall.2] at h'
      omega
    have he4deg : eu.natDegree ≤ 4 := by
      have h := hzero.2.2.2.1
      have h' : (expand k 60 eu).natDegree ≤ 6 * n - g - 120 := by
        rw [← heexpand]
        exact h
      rw [natDegree_expand, hwall.1, hwall.2] at h'
      omega
    exact fiveToSix_exactSix_cOnly_positive_source_false68
      alpha gamma epsilon zeta eta i4 i3 A B cu du eu hA4 hBpoly
      hc2deg hd2deg he4deg ha4 hcTop hi4 hi3 hrow0pos hrow1 hrow2
  · have hb0 : B.coeff 0 ≠ 0 := by
      have h := hnz.2.2.1
      change Be.coeff (3 * n - g) ≠ 0 at h
      simpa [Be, hwall.1, hwall.2, coeff_expand] using h
    have hcTop : cu.coeff 2 ≠ 0 := by
      have h := hnz.2.2.2.1
      change ce.coeff (4 * n - g) ≠ 0 at h
      simpa [hwall.1, hwall.2, hcexpand, coeff_expand] using h
    have hd3 : du.coeff 3 ≠ 0 := by
      have h := hnz.2.2.2.2.1
      change d.coeff (5 * n - g - 60) ≠ 0 at h
      simpa [hwall.1, hwall.2, hdexpand, coeff_expand] using h
    have he5 : eu.coeff 5 ≠ 0 := by
      have h := hnz.2.2.2.2.2.1
      change ee.coeff (6 * n - g - 60) ≠ 0 at h
      simpa [hwall.1, hwall.2, heexpand, coeff_expand] using h
    have hdisc : A.coeff 4 * B.coeff 0 ^ 2 +
        3 * cu.coeff 2 ^ 2 = 0 := by
      have h := hnz.2.2.2.2.2.2.1
      change Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 at h
      simpa [Ae, Be, hwall.1, hwall.2, hcexpand, coeff_expand] using h
    have hi4five := congrArg (fun p : k[X] => p.coeff 5) hi4
    rw [fiveToSix_alignedSmall_i4_coeff_five68 gamma epsilon zeta
      A B cu du eu hA4 hB0deg hc2deg hd3deg he5deg] at hi4five
    norm_num [coeff_C] at hi4five
    have hface : B.coeff 0 * eu.coeff 5 +
        cu.coeff 2 * du.coeff 3 = 0 := by
      exact hi4five
    let C1 : k[X] := (1 / 3 : k) • A ^ 2 + cu
    let D1 : k[X] := (1 / 3 : k) • (A * B) + du
    let E1 : k[X] :=
      (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * cu) + eu
    have hrowOneSource : lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C1 D1 E1)
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C1 D1 E1)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C1 D1 E1) C1 D1 E1 = 0 := by
      have hcoords := integratedPolynomial68_cubicCoordinates
        (0 : k) alpha 0 gamma 0 epsilon zeta eta A B cu D1 eu
      change lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C1 D1 E1)
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C1 D1 E1)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C1 D1 E1) C1 D1 E1 = 0
      rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
        cubicRowOnePolynomial68_split,
        cubicHomogeneousRowOnePolynomial68_residualCoordinates]
      simpa only [C1, D1, E1] using hrow1
    exact fiveToSix_aligned_secondJet_smallChart_rowOne_source_false68
      alpha gamma epsilon zeta eta i4 i3 A B cu du eu hA4 hB0deg
      hc2deg hd3deg he5deg ha4 hb0 hcTop hd3 he5 hface hdisc hi4 hi3
      (hrow0pos 11 (by norm_num)) hrowOneSource

#print axioms fiveToSix_exactSix_cOnly_positive_source_false68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_offsetOneTwenty_source_impossible68

end LaterDeepLowerParentFiveToSixGlobalSourceClosure68

end Max11DegreeRoutes
