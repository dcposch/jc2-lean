import LowScale68SecondaryLaterDeepFiveToSixLowerCoefficient

/-! # One more residual descent in the five-to-six chamber

The zero first residual edge is descended once more, to gap `g+2`.  We also
record that the leading residual row-one coefficient on the nonzero gap
`g+1` packet is exactly a scalar multiple of the already-known I3 incidence
equation, so it supplies no new independent scalar at that degree.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixResidualNext68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 22000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Quartic residual coefficient at the second strict lower edge `g+2`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_gap_two_fiveToSix
    (B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 2)
    (he : e.natDegree ≤ 6 * n - g - 2) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - 2) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 2) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 2)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - 2) hB he
  have hBei : (3 * n - g) + (6 * n - g - 2) =
      9 * n - 2 * g - 2 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - 2) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - 2) =
      9 * n - 2 * g - 2 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Cubic residual coefficient at the same second lower edge. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_gap_two_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 2)
    (he : e.natDegree ≤ 6 * n - g - 2) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 2 * g - 2) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 2)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 2)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g - 2) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g - 2) =
      10 * n - 2 * g - 2 := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - g - 2) hc he
  have hcei : (4 * n - g) + (6 * n - g - 2) =
      10 * n - 2 * g - 2 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 2 * g - 2 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- Literal I4 coefficient at gap `g+2`; the actual source radius bound
`n≥10` keeps `zeta*A` strictly below it. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_gap_two_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hnTen : 10 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 2)
    (he : e.natDegree ≤ 6 * n - g - 2) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - 2) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 2) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 2)) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_gap_two_fiveToSix
      B c d e n g hn hwindow hB hc hd he]
  have hloadA : (zeta • A).natDegree < 9 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - 2 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadA,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  ring

/-- Literal I3 coefficient at gap `g+2`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_gap_two_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 2)
    (he : e.natDegree ≤ 6 * n - g - 2) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - 2) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 2)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 2)) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_gap_two_fiveToSix
      A B c d e n g hn hwindow hA hB hc hd he]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - 2 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - 2 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- Exact residual incidence face at gap `g+2`. -/
theorem polynomialSecondaryResidualGapTwoFace68_fiveToSix
    (gamma epsilon zeta i4 i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hnTen : 10 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 2)
    (he : e.natDegree ≤ 6 * n - g - 2)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - g - 2))
      (e.coeff (6 * n - g - 2)) := by
  constructor
  · have hz := congrArg
      (fun p : k[X] => p.coeff (9 * n - 2 * g - 2)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_gap_two_fiveToSix
      gamma epsilon zeta A B c d e n g hn hnTen hwindow
      hA hB hc hd he] at hz
    have hj : 9 * n - 2 * g - 2 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg
      (fun p : k[X] => p.coeff (10 * n - 2 * g - 2)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_gap_two_fiveToSix
      gamma epsilon zeta A B c d e n g hn hwindow hA hB hc hd he] at hz
    have hj : 10 * n - 2 * g - 2 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

/-! ## The first row-one coefficient on the nonzero `g+1` packet -/

/-- The homogeneous residual row-one coefficient at gap `g+1`.  It factors
through the I3 incidence scalar, so it is redundant on the nonzero packet. -/
theorem secondaryResidualRowOnePolynomial68_coeff_gap_succ_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 2 * g - 2) =
      (-8 / 27 : k) * A.coeff (2 * n) *
        (10 * (n : k) - 2 * (g : k) - 1) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) *
              d.coeff (5 * n - g - 1) -
            3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 1)) := by
  let j := 12 * n - 2 * g - 2
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * derivative d).coeff j =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - g - 1) * (((5 * n - g - 1 : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
      (4 * n) (3 * n - g) (5 * n - g - 1) (by omega)
      hA2deg hB hd
    have hi : 4 * n + (3 * n - g) + (5 * n - g - 1) - 1 = j := by
      dsimp only [j]
      omega
    rw [hi, hA2] at h
    exact h
  have h2 : (A ^ 2 * derivative B * d).coeff j =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - g - 1) * (((3 * n - g : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds_nonneg68 (A ^ 2) d B
      (4 * n) (5 * n - g - 1) (3 * n - g) hA2deg hd hB
    have hi : 4 * n + (5 * n - g - 1) + (3 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    rw [hi, hA2] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have h3 : (A * derivative A * B * d).coeff j =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - g - 1) * (((2 * n : ℕ) : k)) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 B d A A
      (3 * n - g) (5 * n - g - 1) (2 * n) (2 * n) (by omega)
      hB hd hA hA
    have hi : (3 * n - g) + (5 * n - g - 1) + 2 * n + 2 * n - 1 =
        j := by dsimp only [j]; omega
    rw [hi] at h
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
  have h4 : (A * c * derivative e).coeff j =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g - 1) * (((6 * n - g - 1 : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c e
      (2 * n) (4 * n - g) (6 * n - g - 1) (by omega) hA hc he
    have hi : 2 * n + (4 * n - g) + (6 * n - g - 1) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hi] using h
  have h5 : (A * derivative c * e).coeff j =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g - 1) * (((4 * n - g : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A e c
      (2 * n) (6 * n - g - 1) (4 * n - g) (by omega) hA he hc
    have hi : 2 * n + (6 * n - g - 1) + (4 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    rw [hi] at h
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hlow1 : (derivative A * B ^ 2 * c).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow2 : (derivative A * d ^ 2).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow3 : (B ^ 2 * derivative e).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow4 : (B * c * derivative d).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow5 : (B * derivative c * d).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow6 : (derivative B * c * d).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow7 : (c ^ 2 * derivative c).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hlow8 : (e * derivative e).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - g - 1 : ℕ) : k)) =
      5 * (n : k) - (g : k) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 5 * n - g),
      Nat.cast_sub (by omega : g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - g - 1 : ℕ) : k)) =
      6 * (n : k) - (g : k) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 6 * n - g),
      Nat.cast_sub (by omega : g ≤ 6 * n)]
    push_cast
    rfl
  dsimp only [j] at h1 h2 h3 h4 h5 hlow1 hlow2 hlow3 hlow4 hlow5 hlow6 hlow7 hlow8
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  ring

/-- The literal row-one load is far below the residual `g+1` coefficient. -/
theorem cubicLoadRowOnePolynomial68_degree_lt_gap_succ_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        12 * n - 2 * g - 2 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let j := 12 * n - 2 * g - 2
  have hD0 : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  rw [cubicLoadRowOnePolynomial68_zero_beta_delta_exact]
  change ((2 / 3 * gamma : k) • (B * derivative D0 - D0 * derivative B) +
      (4 / 3 * gamma : k) • (A * derivative e) -
      (4 / 3 * gamma : k) • (c * derivative c) +
      (2 / 3 * epsilon : k) • (A * derivative c) +
      (2 * epsilon : k) • derivative e + zeta • derivative D0).natDegree < j
  have hBD : (B * derivative D0).natDegree < j :=
    deepGap_natDegree_mul_derivative_lt68 B D0 (3 * n - g)
      (5 * n - g) j (by omega) hB hD0 (by dsimp only [j]; omega)
  have hDB : (D0 * derivative B).natDegree < j := by
    by_cases hu : 0 < 3 * n - g
    · exact deepGap_natDegree_mul_derivative_lt68 D0 B (5 * n - g)
        (3 * n - g) j hu hD0 hB (by dsimp only [j]; omega)
    · have hu0 : 3 * n - g = 0 := Nat.eq_zero_of_not_pos hu
      have hBconst : B = C (B.coeff 0) := by
        apply eq_C_of_natDegree_le_zero
        simpa only [hu0] using hB
      rw [hBconst, derivative_C, mul_zero]
      simpa only [natDegree_zero] using (show 0 < j by
        dsimp only [j]
        omega)
  have hW := deepGap_natDegree_sub_lt hBD hDB
  have hAe : (A * derivative e).natDegree < j :=
    deepGap_natDegree_mul_derivative_lt68 A e (2 * n)
      (6 * n - g - 1) j (by omega) hA he (by dsimp only [j]; omega)
  have hcc : (c * derivative c).natDegree < j :=
    deepGap_natDegree_mul_derivative_lt68 c c (4 * n - g)
      (4 * n - g) j (by omega) hc hc (by dsimp only [j]; omega)
  have hAc : (A * derivative c).natDegree < j :=
    deepGap_natDegree_mul_derivative_lt68 A c (2 * n)
      (4 * n - g) j (by omega) hA hc (by dsimp only [j]; omega)
  have he' : (derivative e).natDegree < j := by
    have h := natDegree_derivative_le e
    dsimp only [j]
    omega
  have hD' : (derivative D0).natDegree < j := by
    have h := natDegree_derivative_le D0
    dsimp only [j]
    omega
  have hWs := deepGap_natDegree_smul_lt68 (2 / 3 * gamma : k) hW
  have hAes := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hAe
  have hccs := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hcc
  have hAcs := deepGap_natDegree_smul_lt68 (2 / 3 * epsilon : k) hAc
  have hes := deepGap_natDegree_smul_lt68 (2 * epsilon : k) he'
  have hDs := deepGap_natDegree_smul_lt68 zeta hD'
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_add_lt hWs hAes) hccs) hAcs) hes) hDs

/-- Literal integrated row-one coefficient on the residual `g+1` edge. -/
theorem integratedLowerRowOnePolynomial68_coeff_gap_succ_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1) :
    let C0 := (1 / 3 : k) • A ^ 2 + c
    let D0 := (1 / 3 : k) • (A * B) + d
    let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D0 E0)
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B C0 D0 E0) C0 D0 E0).coeff (12 * n - 2 * g - 2) =
      (-8 / 27 : k) * A.coeff (2 * n) *
        (10 * (n : k) - 2 * (g : k) - 1) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) *
              d.coeff (5 * n - g - 1) -
            3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 1)) := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c D0 e
  change (lowerRowOnePolynomial68 _ _ _ C0 D0 E0).coeff _ = _
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_gap_succ_fiveToSix
      A B c d e n g hn hwindow hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_gap_succ_fiveToSix
        alpha gamma epsilon zeta eta A B c d e n g hn hwindow
        hA hB hc hd he), add_zero]

/-- Consequently the first available row-one coefficient vanishes for the
already-known I3 incidence reason; it cannot eliminate packet B. -/
theorem integratedLowerRowOnePolynomial68_gap_succ_redundant_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 1)
    (he : e.natDegree ≤ 6 * n - g - 1)
    (hface : SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - g - 1))
      (e.coeff (6 * n - g - 1))) :
    let C0 := (1 / 3 : k) • A ^ 2 + c
    let D0 := (1 / 3 : k) • (A * B) + d
    let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D0 E0)
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B C0 D0 E0) C0 D0 E0).coeff (12 * n - 2 * g - 2) = 0 := by
  dsimp only
  rw [integratedLowerRowOnePolynomial68_coeff_gap_succ_fiveToSix
    alpha gamma epsilon zeta eta A B c d e n g hn hwindow
    hA hB hc hd he]
  have hrel : A.coeff (2 * n) * B.coeff (3 * n - g) *
      d.coeff (5 * n - g - 1) -
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 1) = 0 := by
    linear_combination -hface.three
  simp only [hrel, mul_zero]

/-- Three-way refinement after descending the zero first edge. -/
def FiveToSixResidualNextPacket68
    (a b c dTop eTop d1 e1 d2 e2 : k) : Prop :=
  (b ≠ 0 ∧ c ≠ 0 ∧ d1 ≠ 0 ∧ e1 ≠ 0 ∧
      a * b ^ 2 + 3 * c ^ 2 = 0) ∨
  (d1 = 0 ∧ e1 = 0 ∧ d2 = 0 ∧ e2 = 0) ∨
  (d1 = 0 ∧ e1 = 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d2 ≠ 0 ∧ e2 ≠ 0 ∧
      a * b ^ 2 + 3 * c ^ 2 = 0)

theorem firstSecondary_gapSucc_gapTwo_refine68
    (a b c dTop eTop d1 e1 d2 e2 : k) (ha : a ≠ 0)
    (hold : (b ≠ 0 ∧ dTop ≠ 0) ∨
      (b = 0 ∧ dTop = 0 ∧ c ≠ 0))
    (hfirst : (d1 = 0 ∧ e1 = 0) ∨
      (b ≠ 0 ∧ c ≠ 0 ∧ d1 ≠ 0 ∧ e1 ≠ 0 ∧
        a * b ^ 2 + 3 * c ^ 2 = 0))
    (hsecond : SecondaryResidualBetweenFace68 a b c d2 e2) :
    FiveToSixResidualNextPacket68 a b c dTop eTop d1 e1 d2 e2 := by
  rcases hfirst with hzero | hnonzero
  · have hclass := firstSecondary_mainFamily_gapSucc_classify68
      a b c dTop eTop d2 e2 ha hold hsecond
    rcases hclass with hzero2 | hnonzero2
    · exact Or.inr (Or.inl ⟨hzero.1, hzero.2, hzero2.1, hzero2.2⟩)
    · exact Or.inr (Or.inr ⟨hzero.1, hzero.2, hnonzero2.1,
        hnonzero2.2.1, hnonzero2.2.2.1, hnonzero2.2.2.2.1,
        hnonzero2.2.2.2.2⟩)
  · exact Or.inl hnonzero

set_option maxHeartbeats 32000000 in
/-- Source-facing refinement: a nonzero first edge remains as the
discriminant packet, while a zero first edge either drops once more or enters
the same discriminant packet at the second edge. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_residualNext68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
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
    FiveToSixResidualNextPacket68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 1))
      (ee.coeff (6 * n - g - 1)) (d.coeff (5 * n - g - 2))
      (ee.coeff (6 * n - g - 2)) := by
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
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change FiveToSixResidualNextPacket68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 1))
    (ee.coeff (6 * n - g - 1)) (d.coeff (5 * n - g - 2))
    (ee.coeff (6 * n - g - 2))
  have hpacket :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_gapSuccPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - 1))
      (ee.coeff (6 * n - g - 1)) ∧ _ at hpacket
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hmain
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0) at hsecondary
  have hold := firstSecondary_mainFamily_attainment_split68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) data.ha hmain hsecondary.2.2.2.2.2
  rcases hpacket.2.2.2 with hfirstZero | hfirstNonzero
  · have hd : d.natDegree ≤ 5 * n - g - 2 := by
      have hd1 : d.natDegree ≤ 5 * n - g - 1 := by omega
      have hpred := natDegree_le_pred hd1 hfirstZero.1
      omega
    have he : ee.natDegree ≤ 6 * n - g - 2 := by
      have he1 : ee.natDegree ≤ 6 * n - g - 1 := by omega
      have hpred := natDegree_le_pred he1 hfirstZero.2
      omega
    have hnTen : 10 ≤ n := by
      simpa only [n] using weightedRadius68_ge_ten A B C0 D E data.hn
    have hgt3 : 3 * n < 2 * g := by omega
    have hlbeta :=
      maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
    have hl : l = 0 := hlbeta.1
    have hbeta : beta = 0 := hlbeta.2
    obtain ⟨i4, hI4raw⟩ := data.invariant
    have hI4 := hI4raw
    rw [hl, hbeta] at hI4
    have hdelta :=
      cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
        gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
        hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    obtain ⟨i3, hi3raw⟩ := hsys.firstThree
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hl, hbeta, hdelta] at hi3e
    rw [hdelta] at hI4
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    rw [hDrec] at hI4 hi3e
    have hsecond := polynomialSecondaryResidualGapTwoFace68_fiveToSix
      gamma epsilon zeta i4 i3 Ae Be ce d ee n g data.hn hnTen hwindow
      data.hA data.hB data.hc hd he hI4 hi3e
    exact firstSecondary_gapSucc_gapTwo_refine68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 1))
      (ee.coeff (6 * n - g - 1)) (d.coeff (5 * n - g - 2))
      (ee.coeff (6 * n - g - 2)) data.ha hold (Or.inl hfirstZero) hsecond
  · exact Or.inl hfirstNonzero

end LaterDeepFiveToSixResidualNext68

#print axioms cubicFirstIntegralFourPolynomial68_coeff_gap_two_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_gap_two_fiveToSix
#print axioms polynomialSecondaryResidualGapTwoFace68_fiveToSix
#print axioms secondaryResidualRowOnePolynomial68_coeff_gap_succ_fiveToSix
#print axioms integratedLowerRowOnePolynomial68_coeff_gap_succ_fiveToSix
#print axioms integratedLowerRowOnePolynomial68_gap_succ_redundant_fiveToSix
#print axioms firstSecondary_gapSucc_gapTwo_refine68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_residualNext68

end Max11DegreeRoutes
