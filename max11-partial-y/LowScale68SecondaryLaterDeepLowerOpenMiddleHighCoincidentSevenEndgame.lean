import LowScale68SecondaryLaterDeepLowerOpenMiddleHighRightSevenRowOne

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_degree_le_twoRadius_of_coincidentSeven
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 2 * n := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma 0 epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
    at hQeq
  rw [hQeq]
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
theorem residualIncidenceQ68_coeff_twoRadius_of_coincidentSeven
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (2 * n) =
      -(3 / 8 : k) * zeta * A.coeff (2 * n) := by
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    0 gamma 0 epsilon zeta i4 A B c d e hi4
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
    at hQeq
  have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
  have hdlt : d.natDegree < 2 * n := hd.trans_lt (by omega)
  have hindex : 2 * n ≠ 0 := by omega
  rw [hQeq, coeff_smul, coeff_sub, coeff_C, if_neg hindex,
    coeff_add, coeff_add, coeff_smul, coeff_smul, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hdlt]
  ring

/-! ## Row zero at `6n-1` -/

def coincidentSevenRowZeroLoad68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e +
    zeta • derivative
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowZeroPolynomial68_coincidentSeven
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e =
      coincidentSevenRowZeroLoad68 gamma epsilon zeta A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, fiveRadiusTerminalRowZeroLoad68,
    coincidentSevenRowZeroLoad68,
    zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem fiveRadiusTerminalRowZeroLoad68_degree_lt_sixRadius_of_coincidentSeven
    (gamma epsilon : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusTerminalRowZeroLoad68 gamma epsilon A B c d e).natDegree <
      6 * n - 1 := by
  simp only [fiveRadiusTerminalRowZeroLoad68]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
theorem coincidentSevenRowZeroLoad68_coeff
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (coincidentSevenRowZeroLoad68 gamma epsilon zeta A B c d e).coeff
        (6 * n - 1) =
      (2 / 9 : k) * (n : k) * zeta * A.coeff (2 * n) ^ 3 := by
  have hlow :=
    fiveRadiusTerminalRowZeroLoad68_degree_lt_sixRadius_of_coincidentSeven
      gamma epsilon A B c d e n g h hn hg hwallH hwallG hA hB hc hd he
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by
    compute_degree
    omega
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have ht := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using ht
  have hAclt : (A * c).natDegree < 6 * n := by
    compute_degree
    omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have htop :
      (((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e).coeff
        (6 * n)) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hder := coeff_derivative_at_bound68
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (6 * n) (by omega)
  rw [htop] at hder
  simp only [coincidentSevenRowZeroLoad68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hlow, zero_add, coeff_smul, smul_eq_mul,
    hder]
  push_cast
  ring

set_option maxHeartbeats 12000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_coincidentSeven
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 2 * n) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (6 * n - 1) =
      (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) *
            (residualIncidenceQ68 B c d e).coeff (2 * n)) -
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h))) := by
  let Q := residualIncidenceQ68 B c d e
  let idx := 6 * n - 1
  change (secondaryResidualRowZeroPolynomial68 A B c d e).coeff idx =
    (4 / 27 : k) * ((2 : k) * (n : k) * A.coeff (2 * n) *
      (-(A.coeff (2 * n) * Q.coeff (2 * n)) -
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
        B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)))
  have hAQ := coeff_mul_mul_derivative_at_bounds68 A Q A
    (2 * n) (2 * n) (2 * n) (by omega) hA hQ hA
  have hiAQ : 2 * n + 2 * n + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAQ] at hAQ
  have hAQ' : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * Q).coeff idx =
        (A * Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAQ
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have ht := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using ht
  have hAB3 := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAB3 : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB3, hB3] at hAB3
  have hAB3' : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (A * derivative A * B ^ 3).coeff idx =
        (A * B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hAB3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have ht := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using ht
  have hBc2 := coeff_mul_mul_derivative_at_bounds68 B (c ^ 2) A
    (3 * n - g) (8 * n - 2 * g) (2 * n) (by omega) hB hc2deg hA
  have hiBc2 : (3 * n - g) + (8 * n - 2 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiBc2, hc2] at hBc2
  have hBc2' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B * c ^ 2).coeff idx =
        (B * c ^ 2 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hBc2
  have hAde := coeff_mul_mul_derivative_at_bounds68 d e A
    (5 * n - h) (6 * n - h) (2 * n) (by omega) hd he hA
  have hiAde : (5 * n - h) + (6 * n - h) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAde] at hAde
  have hAde' : (derivative A * d * e).coeff idx =
      A.coeff (2 * n) * d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * d * e).coeff idx =
        (d * e * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAde
  have h0d : (A * B ^ 2 * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Bd : (A * B * derivative B * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Be : (B * c * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0dd : (B * d * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0Bd2 : (derivative B * d ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have h0cc : (c * derivative c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBe_cd := residualRowZero_Be_cd_eq_Q A B c d e
  have hBe :
      (A * derivative A * B * e + A * derivative A * c * d).coeff idx =
        (A * derivative A * Q).coeff idx +
          ((1 / 9 : k) • (A * derivative A * B ^ 3)).coeff idx := by
    have ht := congrArg (fun p : k[X] => p.coeff idx) hBe_cd
    simpa only [Q, coeff_add, coeff_smul] using ht
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hinner :
      (-(1 : k) • (A * derivative A * B * e) -
          A * derivative A * c * d -
          A * B ^ 2 * derivative d -
          A * B * derivative B * d +
          derivative A * B * c ^ 2 -
          (3 : k) • (derivative A * d * e) +
          (3 : k) • (B * c * derivative e) -
          (3 : k) • (B * d * derivative d) -
          (3 : k) • (derivative B * d ^ 2) -
          (3 : k) • (c * derivative c * d)).coeff idx =
        (2 : k) * (n : k) * A.coeff (2 * n) *
          (-(A.coeff (2 * n) * Q.coeff (2 * n)) -
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 / 9 +
            B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
            (3 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
    simp only [coeff_smul, smul_eq_mul, coeff_add, coeff_sub,
      coeff_eq_zero_of_natDegree_lt h0d,
      coeff_eq_zero_of_natDegree_lt h0Bd,
      coeff_eq_zero_of_natDegree_lt h0Be,
      coeff_eq_zero_of_natDegree_lt h0dd,
      coeff_eq_zero_of_natDegree_lt h0Bd2,
      coeff_eq_zero_of_natDegree_lt h0cc, mul_zero]
    have hsum :
        -1 * (A * derivative A * B * e).coeff idx -
            (A * derivative A * c * d).coeff idx =
          -((A * derivative A * B * e +
            A * derivative A * c * d).coeff idx) := by
      rw [coeff_add]
      ring
    rw [hsum, hBe, coeff_smul, smul_eq_mul, hAQ', hAB3', hBc2', hAde',
      hcast2]
    ring
  rw [secondaryResidualRowZeroPolynomial68, coeff_smul, smul_eq_mul, hinner]

set_option maxHeartbeats 5000000 in
theorem coincidentSeven_rowZero_relation68
    (alpha gamma epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrow0 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) = 0) :
    (32 / 81 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (8 / 9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) +
      (1 / 3 : k) * zeta * A.coeff (2 * n) ^ 2 = 0 := by
  have hQ := residualIncidenceQ68_degree_le_twoRadius_of_coincidentSeven
    gamma epsilon zeta i4 A B c d e n g h hn hwallH hwallG hA hB hd hi4
  have hq := residualIncidenceQ68_coeff_twoRadius_of_coincidentSeven
    gamma epsilon zeta i4 A B c d e n g h hn hwallH hwallG hA hB hd hi4
  have hres := secondaryResidualRowZeroPolynomial68_coeff_coincidentSeven
    A B c d e n g h hn hg hgh hh hwallH hwallG hA hB hc hd he hQ
  have hload := coincidentSevenRowZeroLoad68_coeff
    gamma epsilon zeta A B c d e n g h hn hg hwallH hwallG hA hB hc hd he
  have hloadEq := cubicLoadRowZeroPolynomial68_coincidentSeven
    alpha gamma epsilon zeta eta A B c d e
  rw [coeff_add, hres, hloadEq, hload, hq] at hrow0
  push_cast at hrow0
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hfac : (n : k) * A.coeff (2 * n) ≠ 0 := mul_ne_zero hN ha
  have hfactor : (n : k) * A.coeff (2 * n) *
      ((32 / 81 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (8 / 9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (1 / 3 : k) * zeta * A.coeff (2 * n) ^ 2) = 0 := by
    linear_combination hrow0 +
      (8 / 243 : k) * (n : k) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * hdisc
  exact (mul_eq_zero.mp hfactor).resolve_left hfac

theorem coincidentSeven_balancedRelation_of_rowZero_rowTwo68
    (zeta : k) (a b c d e : k) (n : ℕ) (hn : 0 < n)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0)
    (hrow0 :
      (32 / 81 : k) * b * c ^ 2 - (8 / 9 : k) * d * e +
        (1 / 3 : k) * zeta * a ^ 2 = 0)
    (hrow2 :
      (32 / 81 : k) * (((4 * n : ℕ) : k)) * a * b ^ 3 +
        (8 / 3 : k) * (((4 * n : ℕ) : k)) * d * e +
        zeta * (n : k) * a ^ 2 = 0) :
    (4 : k) * b * c ^ 2 - (9 : k) * d * e = 0 := by
  push_cast at hrow2
  have hN : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hR2fac : (n : k) *
      ((-128 / 27 : k) * b * c ^ 2 + (32 / 3 : k) * d * e +
        zeta * a ^ 2) = 0 := by
    linear_combination hrow2 -
      (128 / 81 : k) * (n : k) * b * hdisc
  have hR2 :
      (-128 / 27 : k) * b * c ^ 2 + (32 / 3 : k) * d * e +
        zeta * a ^ 2 = 0 :=
    (mul_eq_zero.mp hR2fac).resolve_left hN
  have hfac : (40 / 27 : k) ≠ 0 := by norm_num
  have hbalanced : (40 / 27 : k) *
      ((4 : k) * b * c ^ 2 - (9 : k) * d * e) = 0 := by
    linear_combination (3 : k) * hrow0 - hR2
  exact (mul_eq_zero.mp hbalanced).resolve_left hfac

/-! ## Row one after the row-zero/row-two cancellation -/

def fiveRadiusCoincidentSevenRowOneTail68
    (gamma epsilon zeta : k) (A B c d e : k[X]) : k[X] :=
  fiveRadiusBalancedRowOneTail68 gamma epsilon A B c d e +
    zeta • ((1 / 3 : k) • (derivative A * B) + derivative d)

theorem fiveRadiusReducedRowOnePolynomial68_coincidentSevenSplit
    (gamma epsilon zeta : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e =
      fiveRadiusBalancedRowOneCore68 A B c d e +
        fiveRadiusCoincidentSevenRowOneTail68 gamma epsilon zeta A B c d e := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusBalancedRowOneCore68, fiveRadiusBalancedRowOneTail68,
    fiveRadiusCoincidentSevenRowOneTail68]
  module

set_option maxHeartbeats 7000000 in
theorem fiveRadiusCoincidentSevenRowOneTail68_degree_lt
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusCoincidentSevenRowOneTail68
      gamma epsilon zeta A B c d e).natDegree < 5 * n - 1 := by
  let idx := 5 * n - 1
  have hBcd : (derivative (B * c * d)).natDegree < idx := by
    have hp : (B * c * d).natDegree ≤ 12 * n - 2 * g - h := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (B * c * d)
    dsimp [idx]
    omega
  have hBp : (derivative B * c * d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBe : (B ^ 2 * derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hBd : (B * derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdB : (d * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB2 : (derivative A * B ^ 2).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hABBp : (A * B * derivative B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hep : (derivative e).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hApB : (derivative A * B).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  have hdp : (derivative d).natDegree < idx := by
    dsimp [idx]
    compute_degree
    omega
  simp only [fiveRadiusCoincidentSevenRowOneTail68,
    fiveRadiusBalancedRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (-4 / 27 : k)
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_smul_lt68 (3 : k) hBcd)
              (deepGap_natDegree_smul_lt68 (6 : k) hBp))
            (deepGap_natDegree_smul_lt68 (-3 : k) hBe)))
        (deepGap_natDegree_smul_lt68 gamma
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_smul_lt68 (2 / 3 : k)
                (deepGap_natDegree_sub_lt
                  (deepGap_natDegree_sub_lt hBd hdB)
                  (deepGap_natDegree_smul_lt68 (2 : k) hcc)))
              (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
            (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp))))
      (deepGap_natDegree_smul_lt68 (2 * epsilon : k) hep))
    (deepGap_natDegree_smul_lt68 zeta
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (1 / 3 : k) hApB) hdp))

set_option maxHeartbeats 11000000 in
theorem fiveRadiusBalancedRowOneCore68_coeff_of_coincidentSeven
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusBalancedRowOneCore68 A B c d e).coeff (5 * n - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 *
                c.coeff (4 * n - g)) * ((5 * n : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) *
            c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hd
  have hd2 : (d ^ 2).coeff (2 * (5 * n - h)) =
      d.coeff (5 * n - h) ^ 2 :=
    coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2)
    (2 * n) (2 * (5 * n - h)) hA hd2deg
  have hiAd2 : 2 * n + 2 * (5 * n - h) = 5 * n := by omega
  rw [hiAd2, hd2] at hAd2
  have hAd2' := coeff_derivative_at_bound68 (A * d ^ 2) (5 * n) (by omega)
  rw [hAd2] at hAd2'
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hB
  have hB2 : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (2 * (3 * n - g)) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + 2 * (3 * n - g) + (4 * n - g) = 5 * n := by
    omega
  rw [hiAB2c, hB2] at hAB2c
  have hAB2c' := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (5 * n) (by omega)
  rw [hAB2c] at hAB2c'
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hic3 : 2 * (4 * n - g) + (4 * n - g) - 1 = 5 * n - 1 := by
    omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 5 * n - 1 := by omega
  rw [hiee] at hee
  simp only [fiveRadiusBalancedRowOneCore68, coeff_smul, coeff_add,
    smul_eq_mul, hAd2', hAB2c', hc3, hee]
  ring

set_option maxHeartbeats 7000000 in
theorem fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hddeg : d.natDegree ≤ 5 * n - h)
    (hedeg : e.natDegree ≤ 6 * n - h)
    (hc : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (fiveRadiusReducedRowOnePolynomial68 gamma epsilon zeta A B c d e).coeff
      (5 * n - 1) ≠ 0 := by
  have htail := fiveRadiusCoincidentSevenRowOneTail68_degree_lt
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hwallH hwallG
    hA hB hcdeg hddeg hedeg
  have hcore := fiveRadiusBalancedRowOneCore68_coeff_of_coincidentSeven
    A B c d e n g h hn hg hwallH hwallG hA hB hcdeg hddeg hedeg
  rw [fiveRadiusReducedRowOnePolynomial68_coincidentSevenSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hbal : 2 * h = 3 * g := by omega
  have hbalK : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    exact_mod_cast hbal
  have hng : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    have hpos : 0 < 4 * n - g := by omega
    have hcast : (((4 * n - g : ℕ) : k)) =
        (4 : k) * (n : k) - (g : k) := by
      rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
      push_cast
      ring
    rw [← hcast]
    exact Nat.cast_ne_zero.mpr hpos.ne'
  have hscalar := residualRowOneScalar_ne_zero68
    (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hng hbalK hdisc hinc hrel
  have heq := residualRowOneScalar68
    (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) hc hbalK hdisc hinc hrel
  intro hz
  apply hscalar
  rw [← heq]
  rw [Nat.cast_sub (by omega : g ≤ 4 * n),
    Nat.cast_sub (by omega : h ≤ 6 * n)] at hz
  push_cast at hz
  have hwallGK : (3 : k) * (g : k) = (7 : k) * (n : k) := by
    exact_mod_cast hwallG
  have hfiveK : (12 : k) * (n : k) - (3 : k) * (g : k) =
      (5 : k) * (n : k) := by
    linear_combination -hwallGK
  rw [hfiveK]
  exact hz

set_option maxHeartbeats 16000000 in
theorem laterDeepLowerOpenMiddle_coincidentSeven_impossible68
    (alpha gamma epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow2 : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68
        0 alpha 0 gamma 0 epsilon zeta eta A B c
          ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow0 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) = 0) :
    False := by
  have hsum : g + h < 7 * n := by omega
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
      gamma epsilon zeta A B c d e n g h hn hopen hsum hA hB hd
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
      gamma epsilon zeta i4 i3 A B c d e n g h hn hg hgh hh hopen
      hload hA hB hc hd he hi4 hi3
  have hrow0rel := coincidentSeven_rowZero_relation68
    alpha gamma epsilon zeta eta i4 A B c d e n g h hn hg hgh hh
    hwallH hwallG ha hA hB hc hd he hdisc hi4 hrow0
  have hrow2rel := fiveRadiusReducedRowTwo_coincidentSevenWalls_relation68
    gamma epsilon zeta i4 A B c d e n g h hn hg hgh hopen hwallH hwallG
    hA hB hc hd he hdisc hrow2
  have hrel := coincidentSeven_balancedRelation_of_rowZero_rowTwo68
    zeta (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) n hn hdisc hrow0rel hrow2rel
  have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
    alpha gamma epsilon zeta eta i3 A B c d e hi3 hrow1
  have hne := fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
    gamma epsilon zeta A B c d e n g h hn hg hgh hh hwallH hwallG
    hA hB hc hd he hc0 hdisc face.four hrel
  have hz := congrArg (fun p : k[X] => p.coeff (5 * n - 1)) hreduced
  simp only [coeff_zero] at hz
  exact hne hz

/-! ## Source-facing closure -/

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentSeven_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hmiddle :
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
      let h := secondaryResidualGap68 n d ee
      h < 2 * g)
    (hseven :
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
      let h := secondaryResidualGap68 n d ee
      2 * h = 7 * n ∧ 3 * g = 7 * n) : False := by
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
  let h := secondaryResidualGap68 n d ee
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change h < 2 * g at hmiddle
  change 2 * h = 7 * n ∧ 3 * g = 7 * n at hseven
  have hhigh5 : 5 * n < 2 * h ∧ 5 * n < 3 * g := by omega
  have hdelta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighStrict_forces_delta68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hhigh5)
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧ _ at ordinary
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hg : 0 < g := secondary.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, ordinary.1, ordinary.2.1, hdelta] at hi4e
    exact hi4e
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, ordinary.1, ordinary.2.1, hdelta] at hi3e
    exact hi3e
  have hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at hrowTwo
  have hrow2r := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow2r
  have hred2 : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon zeta eta i4 Ae Be ce d ee hi4c hrow2r
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  rw [hCrec, hDrec, hErec] at h1e
  have hrow1 := polynomialSecondaryResidualRowOne68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow1
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h0e
  have hsplit0 := cubicRowZeroPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum0 :
      secondaryResidualRowZeroPolynomial68 Ae Be ce d ee +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee =
        C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa using hsplit0.symm.trans h0e
  have hidx : 6 * n - 1 ≠ 59 := by omega
  have hterm :
      (C terminal * (60 * (X ^ 59 : k[X]))).coeff (6 * n - 1) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, hidx]
  have hrow0 := congrArg (fun p : k[X] => p.coeff (6 * n - 1)) hsum0
  rw [ordinary.1, ordinary.2.1, hdelta, coeff_add, hterm] at hrow0
  exact laterDeepLowerOpenMiddle_coincidentSeven_impossible68
    alpha gamma epsilon zeta eta i4 i3 Ae Be ce d ee n g h hn hg
    ordinary.2.2.1 hmiddle hopen hseven.1 hseven.2 ha
    ordinary.2.2.2.2.2.2.1 hA secondary.2.1 secondary.2.2.1
    ordinary.2.2.2.1 ordinary.2.2.2.2.1
    ordinary.2.2.2.2.2.2.2.2.2 hi4c hi3c hred2 hrow1 hrow0

#print axioms residualIncidenceQ68_degree_le_twoRadius_of_coincidentSeven
#print axioms residualIncidenceQ68_coeff_twoRadius_of_coincidentSeven
#print axioms cubicLoadRowZeroPolynomial68_coincidentSeven
#print axioms secondaryResidualRowZeroPolynomial68_coeff_coincidentSeven
#print axioms coincidentSeven_rowZero_relation68
#print axioms coincidentSeven_balancedRelation_of_rowZero_rowTwo68
#print axioms fiveRadiusReducedRowOnePolynomial68_coeff_coincidentSeven_ne_zero
#print axioms laterDeepLowerOpenMiddle_coincidentSeven_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentSeven_impossible68

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

end Max11DegreeRoutes
