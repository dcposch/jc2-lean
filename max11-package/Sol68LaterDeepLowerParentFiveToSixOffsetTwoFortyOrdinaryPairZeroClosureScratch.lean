import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryNonzeroRowZeroOneClosureScratch

/-! # Offset-240 ordinary pair-zero closure

The terminal pair-zero packet has `d = 0` and constant `e`.  Its two
remaining leaves are closed by literal contracted source rows.  The loaded
I3 wall is incompatible with row-zero coefficient `7` and row-one
coefficient `5`.  If the top `c` edge vanishes, I3 coefficient `1` kills
the next edge; row-zero/row-one coefficient `3` then kill the constant
`c` and `gamma`, and row-two coefficient `3` is nonzero.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryPairZeroClosure68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem fiveToSix_pairZero_rowZero_polynomial68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hB : B.natDegree ≤ 0) (hd : d = 0) (he : e.natDegree ≤ 0) :
    secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e =
      (B.coeff 0 / 27 : k) •
        (derivative A *
          ((4 : k) • c ^ 2 + (6 * gamma : k) • c -
            (4 * e.coeff 0 + 3 * epsilon : k) • A)) := by
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have heC : e = C (e.coeff 0) := eq_C_of_natDegree_le_zero he
  rw [hd, hBC, heC]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [secondaryResidualRowZeroPolynomial68,
    cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, zero_mul, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_smul, derivative_C, one_mul,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast,
    map_one, coeff_C_zero]
  ring

theorem fiveToSix_pairZero_rowOne_polynomial68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hB : B.natDegree ≤ 0) (hd : d = 0) (he : e.natDegree ≤ 0) :
    secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e =
      (2 / 27 : k) •
        ((4 * B.coeff 0 ^ 2 : k) • (derivative A * c) +
          (12 * e.coeff 0 + 9 * epsilon : k) • (A * derivative c) -
          (12 : k) • (c ^ 2 * derivative c) -
          (18 * gamma : k) • (c * derivative c) +
          (3 * gamma * B.coeff 0 ^ 2 : k) • derivative A) := by
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have heC : e = C (e.coeff 0) := eq_C_of_natDegree_le_zero he
  rw [hd, hBC, heC]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [secondaryResidualRowOnePolynomial68,
    cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one,
    coeff_C_zero]
  ring

theorem cubicFirstIntegralThreePolynomial68_coeff_one_pairZero68
    (gamma epsilon : k) (A B c d e : k[X])
    (hB : B.natDegree ≤ 0) (hc : c.natDegree ≤ 1)
    (hd : d = 0) (he : e.natDegree ≤ 0) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 1 =
      c.coeff 1 * ((8 / 3 : k) * e.coeff 0 + 2 * epsilon -
        (8 / 9 : k) * B.coeff 0 ^ 2) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    hd, coeff_sub, coeff_add, coeff_add, coeff_add]
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have heC : e = C (e.coeff 0) := eq_C_of_natDegree_le_zero he
  have hB2c : (B ^ 2 * c).coeff 1 =
      B.coeff 0 ^ 2 * c.coeff 1 := by
    calc
      (B ^ 2 * c).coeff 1 = (C (B.coeff 0) ^ 2 * c).coeff 1 := by
        exact congrArg (fun q : k[X] => (q ^ 2 * c).coeff 1) hBC
      _ = B.coeff 0 ^ 2 * c.coeff 1 := by
        have h0 : (C (B.coeff 0) * C (B.coeff 0)).coeff 0 =
            B.coeff 0 * B.coeff 0 := by simp
        have h1 : (C (B.coeff 0) * C (B.coeff 0)).coeff 1 = 0 := by
          rw [mul_coeff_one]
          norm_num [coeff_C]
        rw [pow_two, mul_coeff_one, h0, h1]
        ring
  have hce : (c * e).coeff 1 = c.coeff 1 * e.coeff 0 := by
    rw [heC]
    simp
  have hd2 : (0 : k[X]) ^ 2 = 0 := by simp
  have hB2deg : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hB2one : (B ^ 2).coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2deg.trans_lt (by norm_num))
  have heone : e.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, coeff_zero, mul_zero, zero_mul,
    add_zero, zero_add, hB2c, hce, hB2one, heone, hd2]
  ring

theorem fiveToSix_pairZero_rowZero_coeff_seven68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d = 0) (he : e.natDegree ≤ 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 =
      (16 / 27 : k) * A.coeff 4 * B.coeff 0 *
        (c.coeff 2 ^ 2 -
          (e.coeff 0 + (3 / 4 : k) * epsilon) * A.coeff 4) := by
  rw [fiveToSix_pairZero_rowZero_polynomial68
    alpha gamma epsilon eta A B c d e hB hd he, coeff_smul, smul_eq_mul]
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hcsq : (c ^ 2).natDegree ≤ 4 := by compute_degree; omega
  have hinner : ((4 : k) • c ^ 2 + (6 * gamma : k) • c -
      (4 * e.coeff 0 + 3 * epsilon : k) • A).coeff 4 =
      4 * c.coeff 2 ^ 2 -
        (4 * e.coeff 0 + 3 * epsilon) * A.coeff 4 := by
    have hc4 := coeff_pow_at_bound68 c 2 2 hc
    norm_num at hc4
    have hcdeg : ((6 * gamma : k) • c).natDegree < 4 := by
      compute_degree; omega
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hc4,
      coeff_eq_zero_of_natDegree_lt hcdeg]
    ring
  have htop := coeff_mul_at_bounds68 (derivative A)
    ((4 : k) • c ^ 2 + (6 * gamma : k) • c -
      (4 * e.coeff 0 + 3 * epsilon : k) • A) 3 4 hderA (by
        compute_degree; omega)
  norm_num [coeff_derivative, hinner] at htop
  rw [htop]
  ring

theorem fiveToSix_pairZero_rowOne_coeff_five68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d = 0) (he : e.natDegree ≤ 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 =
      (8 / 27 : k) *
        (4 * B.coeff 0 ^ 2 * A.coeff 4 * c.coeff 2 +
          6 * e.coeff 0 * A.coeff 4 * c.coeff 2 -
          6 * c.coeff 2 ^ 3) +
        (4 / 3 : k) * epsilon * A.coeff 4 * c.coeff 2 := by
  rw [fiveToSix_pairZero_rowOne_polynomial68
    alpha gamma epsilon eta A B c d e hB hd he, coeff_smul, smul_eq_mul]
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hderc : (derivative c).natDegree ≤ 1 := by compute_degree; omega
  have h1 := coeff_mul_at_bounds68 (derivative A) c 3 2 hderA hc
  have h2 := coeff_mul_at_bounds68 A (derivative c) 4 1 hA hderc
  have h3 := coeff_mul_mul_at_bounds68 (c ^ 2) (derivative c) (1 : k[X])
    4 1 0 (by compute_degree; omega) hderc (by norm_num)
  norm_num [coeff_derivative, pow_two, coeff_mul_at_bounds68 c c 2 2 hc hc,
    coeff_one] at h1 h2 h3
  have h3' : (c ^ 2 * derivative c).coeff 5 =
      2 * c.coeff 2 ^ 3 := by
    rw [pow_two]
    linear_combination h3
  have hlow1 : (c * derivative c).natDegree < 5 := by
    compute_degree; omega
  have hlow2 : (derivative A).natDegree < 5 := by
    compute_degree; omega
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, h1, h2, h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2]
  ring

theorem fiveToSix_pairZero_rowZero_coeff_three_of_constant_c68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 0) (hd : d = 0) (he : e.natDegree ≤ 0)
    (hload : 4 * e.coeff 0 + 3 * epsilon = 0) :
    (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 =
      (8 / 27 : k) * A.coeff 4 * B.coeff 0 * c.coeff 0 *
        (2 * c.coeff 0 + 3 * gamma) := by
  rw [fiveToSix_pairZero_rowZero_polynomial68
    alpha gamma epsilon eta A B c d e hB hd he, coeff_smul, smul_eq_mul]
  have hcC : c = C (c.coeff 0) := eq_C_of_natDegree_le_zero hc
  rw [hload, zero_smul, sub_zero, hcC]
  norm_num [derivative_C, coeff_derivative, mul_coeff_three_twoForty68,
    pow_two, coeff_C]
  ring

theorem fiveToSix_pairZero_rowOne_coeff_three_of_constant_c68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 0) (hd : d = 0) (he : e.natDegree ≤ 0)
    (hload : 4 * e.coeff 0 + 3 * epsilon = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 =
      (8 / 27 : k) * B.coeff 0 ^ 2 * A.coeff 4 *
        (4 * c.coeff 0 + 3 * gamma) := by
  rw [fiveToSix_pairZero_rowOne_polynomial68
    alpha gamma epsilon eta A B c d e hB hd he, coeff_smul, smul_eq_mul]
  have hcC : c = C (c.coeff 0) := eq_C_of_natDegree_le_zero hc
  have hload3 : 12 * e.coeff 0 + 9 * epsilon = 0 := by
    linear_combination 3 * hload
  rw [hload3, zero_smul, add_zero, hcC]
  norm_num [derivative_C, coeff_derivative, mul_coeff_three_twoForty68]
  ring

theorem fiveToSix_pairZero_rowTwo_coeff_three_final68
    (alpha epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c = 0) (hd : d = 0) (he : e.natDegree ≤ 0)
    (hload : 4 * e.coeff 0 + 3 * epsilon = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 =
      (16 / 27 : k) * B.coeff 0 ^ 3 * A.coeff 4 := by
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have heC : e = C (e.coeff 0) := eq_C_of_natDegree_le_zero he
  have hepsilon : epsilon = (-4 / 3 : k) * e.coeff 0 := by
    linear_combination (1 / 3 : k) * hload
  have hpoly : secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e =
      (4 / 27 * B.coeff 0 ^ 3 : k) • derivative A := by
    rw [hc, hd, hBC, heC, hepsilon]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [secondaryResidualRowTwoPolynomial68,
      cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
      cubicLoadTPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, zero_mul, zero_smul, smul_zero, add_zero,
      zero_add, sub_zero, derivative_add, derivative_sub, derivative_mul,
      derivative_pow, derivative_smul, derivative_C, one_mul,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat,
      map_natCast, map_one, coeff_C_zero]
    ring
  rw [hpoly, coeff_smul, smul_eq_mul]
  norm_num [coeff_derivative]
  ring

theorem fiveToSix_pairZero_loaded_wall_impossible68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d = 0) (he : e.natDegree ≤ 0)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hwall : 9 * epsilon + 12 * e.coeff 0 - 4 * B.coeff 0 ^ 2 = 0)
    (hrow0 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 = 0)
    (hrow1 : (secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 = 0) : False := by
  rw [fiveToSix_pairZero_rowZero_coeff_seven68
    alpha gamma epsilon eta A B c d e hA hB hc hd he] at hrow0
  have htop : A.coeff 4 * B.coeff 0 ^ 2 - 3 * c.coeff 2 ^ 2 = 0 := by
    have hs : A.coeff 4 * B.coeff 0 *
        (c.coeff 2 ^ 2 -
          (e.coeff 0 + (3 / 4 : k) * epsilon) * A.coeff 4) = 0 := by
      linear_combination (27 / 16 : k) * hrow0
    have hinner := (mul_eq_zero.mp hs).resolve_left (mul_ne_zero ha hb)
    linear_combination (-3 : k) * hinner - (A.coeff 4 / 4 : k) * hwall
  have hcTop : c.coeff 2 ≠ 0 := by
    intro hz
    have hab : A.coeff 4 * B.coeff 0 ^ 2 = 0 := by
      rw [hz] at htop
      linear_combination htop
    exact (mul_ne_zero ha (pow_ne_zero 2 hb)) hab
  rw [fiveToSix_pairZero_rowOne_coeff_five68
    alpha gamma epsilon eta A B c d e hA hB hc hd he] at hrow1
  have hcubic : (32 / 9 : k) * c.coeff 2 ^ 3 = 0 := by
    linear_combination hrow1 -
      (4 / 27 : k) * A.coeff 4 * c.coeff 2 * hwall -
      (16 / 9 : k) * c.coeff 2 * htop
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hcTop)) hcubic

theorem fiveToSix_pairZero_zero_edge_impossible68
    (alpha gamma epsilon eta i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d = 0) (he : e.natDegree ≤ 0)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow7 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 = 0)
    (hrow3 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 = 0)
    (hrowOne3 : (secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 = 0)
    (hrowTwo3 : (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 = 0) : False := by
  have hc1 : c.natDegree ≤ 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      by_cases hn2 : n = 2
      · simpa only [hn2] using hcTop
      · exact coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by omega)))
  rw [fiveToSix_pairZero_rowZero_coeff_seven68
    alpha gamma epsilon eta A B c d e hA hB hc hd he] at hrow7
  rw [hcTop] at hrow7
  have hload : 4 * e.coeff 0 + 3 * epsilon = 0 := by
    have hs : A.coeff 4 * B.coeff 0 *
        ((e.coeff 0 + (3 / 4 : k) * epsilon) * A.coeff 4) = 0 := by
      linear_combination (-27 / 16 : k) * hrow7
    have hin := (mul_eq_zero.mp hs).resolve_left (mul_ne_zero ha hb)
    have hin' := (mul_eq_zero.mp hin).resolve_right ha
    linear_combination 4 * hin'
  have hi3one := congrArg (fun p : k[X] => p.coeff 1) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_one_pairZero68
    gamma epsilon A B c d e hB hc1 hd he] at hi3one
  norm_num [coeff_C] at hi3one
  have hcOne : c.coeff 1 = 0 := by
    rcases hi3one with hzero | hfactor
    · exact hzero
    · have hbzero : B.coeff 0 ^ 2 = 0 := by
        linear_combination (-9 / 8 : k) * hfactor + (3 / 4 : k) * hload
      exact False.elim ((pow_ne_zero 2 hb) hbzero)
  have hc0 : c.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      by_cases hn1 : n = 1
      · simpa only [hn1] using hcOne
      exact coeff_eq_zero_of_natDegree_lt (hc1.trans_lt (by omega)))
  rw [fiveToSix_pairZero_rowZero_coeff_three_of_constant_c68
    alpha gamma epsilon eta A B c d e hA hB hc0 hd he hload] at hrow3
  rw [fiveToSix_pairZero_rowOne_coeff_three_of_constant_c68
    alpha gamma epsilon eta A B c d e hA hB hc0 hd he hload] at hrowOne3
  have hone : 4 * c.coeff 0 + 3 * gamma = 0 := by
    have hs : B.coeff 0 ^ 2 * A.coeff 4 *
        (4 * c.coeff 0 + 3 * gamma) = 0 := by
      linear_combination (27 / 8 : k) * hrowOne3
    exact (mul_eq_zero.mp hs).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hb) ha)
  have hczero : c.coeff 0 = 0 := by
    have hs : c.coeff 0 * (2 * c.coeff 0 + 3 * gamma) = 0 := by
      have hp : A.coeff 4 * B.coeff 0 * c.coeff 0 *
          (2 * c.coeff 0 + 3 * gamma) = 0 := by
        linear_combination (27 / 8 : k) * hrow3
      have hp' : (A.coeff 4 * B.coeff 0) *
          (c.coeff 0 * (2 * c.coeff 0 + 3 * gamma)) = 0 := by
        linear_combination hp
      exact (mul_eq_zero.mp hp').resolve_left (mul_ne_zero ha hb)
    rcases mul_eq_zero.mp hs with hz | hfactor
    · exact hz
    · linear_combination (1 / 2 : k) * hone - (1 / 2 : k) * hfactor
  have hgamma : gamma = 0 := by
    linear_combination (1 / 3 : k) * hone - (4 / 3 : k) * hczero
  have hcpoly : c = 0 := by
    rw [eq_C_of_natDegree_le_zero hc0, hczero]
    simp
  rw [hgamma] at hrowTwo3
  rw [fiveToSix_pairZero_rowTwo_coeff_three_final68
    alpha epsilon eta A B c d e hA hB hcpoly hd he hload] at hrowTwo3
  exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hb)) ha)
    hrowTwo3

set_option maxHeartbeats 22000000 in
theorem fiveToSix_offsetTwoForty_ordinary_pairZero_source_closure68
    (alpha gamma epsilon eta i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d = 0) (he : e.natDegree ≤ 0)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hterminal : c.coeff 2 = 0 ∨
      9 * epsilon + 12 * e.coeff 0 - 4 * B.coeff 0 ^ 2 = 0)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow7 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 = 0)
    (hrowOne5 : (secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 5 = 0)
    (hrow3 : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 = 0)
    (hrowOne3 : (secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 = 0)
    (hrowTwo3 : (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff 3 = 0) : False := by
  rcases hterminal with hcTop | hwall
  · exact fiveToSix_pairZero_zero_edge_impossible68
      alpha gamma epsilon eta i3 A B c d e hA hB hc hd he ha hb hcTop
      hi3 hrow7 hrow3 hrowOne3 hrowTwo3
  · exact fiveToSix_pairZero_loaded_wall_impossible68
      alpha gamma epsilon eta A B c d e hA hB hc hd he ha hb hwall
      hrow7 hrowOne5

#print axioms fiveToSix_pairZero_rowZero_polynomial68
#print axioms fiveToSix_pairZero_rowOne_polynomial68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_one_pairZero68
#print axioms fiveToSix_pairZero_rowZero_coeff_seven68
#print axioms fiveToSix_pairZero_rowOne_coeff_five68
#print axioms fiveToSix_pairZero_rowZero_coeff_three_of_constant_c68
#print axioms fiveToSix_pairZero_rowOne_coeff_three_of_constant_c68
#print axioms fiveToSix_pairZero_rowTwo_coeff_three_final68
#print axioms fiveToSix_pairZero_loaded_wall_impossible68
#print axioms fiveToSix_pairZero_zero_edge_impossible68
#print axioms fiveToSix_offsetTwoForty_ordinary_pairZero_source_closure68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryPairZeroClosure68

end Max11DegreeRoutes
