
/-! ## Unique-`B` tie: `κ` companion cannot drop with `λ` -/

section UniqueBKappa610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_two_km {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three_km {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four_km {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five_km {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

/-- Load-free two-term `κ` face on the unique-`B` tie, written without
nsmul so leading-coefficient arithmetic is direct. -/
def kappaHighBTieExpanded610 (A B : k[X]) : k[X] :=
  (-(35 / 729 : k)) • (A ^ 4 * B) + (20 / 243 : k) • (A * B ^ 3)

/-- `κ` with the unique-`B` tie face deleted. -/
def degreeZeroKappaNoHighBTieRest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(3 / 256 * l : k)) • A ^ 5 +
    (20 / 81 : k) • (A ^ 2 * B * C0) +
    (9 / 64 * l : k) • (A ^ 2 * B ^ 2) +
    (20 / 243 : k) • (A ^ 3 * D0) +
    (3 / 32 * l : k) • (A ^ 3 * C0) +
    (20 / 243 * alpha : k) • (A ^ 3 * B) +
    (385 / 31104 * beta : k) • A ^ 4 -
    (5 / 27 : k) • (B * C0 ^ 2) -
    (5 / 27 : k) • (B ^ 2 * D0) -
    (3 / 16 * l : k) • (B ^ 2 * C0) -
    (4 / 81 * alpha : k) • B ^ 3 -
    (10 / 27 : k) • (A * C0 * D0) -
    (3 / 16 * l : k) • (A * C0 ^ 2) -
    (10 / 27 : k) • (A * B * E0) -
    (3 / 8 * l : k) • (A * B * D0) -
    (8 / 27 * alpha : k) • (A * B * C0) -
    (35 / 432 * beta : k) • (A * B ^ 2) -
    (3 / 16 * l : k) • (A ^ 2 * E0) -
    (4 / 27 * alpha : k) • (A ^ 2 * D0) -
    (35 / 432 * beta : k) • (A ^ 2 * C0) +
    (35 / 1296 * delta : k) • A ^ 3 +
    (10 / 9 : k) • (D0 * E0) +
    (3 / 8 * l : k) • D0 ^ 2 +
    (3 / 4 * l : k) • (C0 * E0) +
    (4 / 9 * alpha : k) • (C0 * D0) +
    (7 / 72 * beta : k) • C0 ^ 2 +
    (4 / 9 * alpha : k) • (B * E0) +
    (7 / 36 * beta : k) • (B * D0) -
    (5 / 72 * delta : k) • B ^ 2 +
    (7 / 36 * beta : k) • (A * E0) -
    (5 / 36 * delta : k) • (A * C0) -
    (2 / 9 * epsilon : k) • (A * B) -
    (1 / 8 * zeta : k) • A ^ 2 +
    (5 / 6 * delta : k) • E0 +
    (2 / 3 * epsilon : k) • D0 +
    (1 / 2 * zeta : k) • C0 +
    (1 / 3 * eta : k) • B +
    (1 / 6 * theta : k) • A

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaPolynomial610_eq_highBTie_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      kappaHighBTieExpanded610 A B +
        degreeZeroKappaNoHighBTieRest610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0 := by
  simp only [degreeZeroKappaPolynomial610, kappaHighBTieExpanded610,
    degreeZeroKappaNoHighBTieRest610]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaNoHighBTieRest610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0) :
    (degreeZeroKappaNoHighBTieRest610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * A.natDegree + B.natDegree := by
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  simp only [degreeZeroKappaNoHighBTieRest610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  have hA1 : A.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hA
  have hC1 : C0.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hC
  have hD1 : D0.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hD
  have hE1 : E0.natDegree + 1 ≤ B.natDegree := Nat.succ_le_of_lt hE
  omega

/-- Leading-coefficient identity: `7 u = 12 v` forces the `λ` combination
`7 u² - 126 u v + 27 v²` to `-8253 v² / 49`. -/
theorem lambda_uv7_of_kappa_factor (u v : k)
    (h : (7 : k) * u = 12 * v) :
    (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) =
      -8253 * v ^ 2 := by
  calc
    (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2)
        = 7 * ((7 * u) * (7 * u) - 882 * u * v + 189 * v ^ 2) := by ring
    _ = 7 * ((12 * v) * (12 * v) - 882 * u * v + 189 * v ^ 2) := by rw [h]
    _ = 7 * (333 * v ^ 2 - 882 * u * v) := by ring
    _ = 2331 * v ^ 2 - 882 * (7 * u) * v := by ring
    _ = 2331 * v ^ 2 - 882 * (12 * v) * v := by rw [h]
    _ = -8253 * v ^ 2 := by ring

theorem lambdaHighBTie_coeff_ne_zero_of_kappa_factor
    {A B : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hkap : (7 : k) * A.leadingCoeff ^ 3 = 12 * B.leadingCoeff ^ 2) :
    (35 / 6561 : k) * A.leadingCoeff ^ 6 -
        (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
          (5 / 243 : k) * B.leadingCoeff ^ 4 ≠
      0 := by
  set u := A.leadingCoeff ^ 3 with hu
  set v := B.leadingCoeff ^ 2 with hv
  have hvne : v ≠ 0 := pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hB)
  have hform :
      (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) =
        -8253 * v ^ 2 :=
    lambda_uv7_of_kappa_factor u v (by simpa [u, v] using hkap)
  have hne : (7 : k) * u ^ 2 - 126 * u * v + 27 * v ^ 2 ≠ 0 := by
    intro hz
    have h49 : (49 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) = 0 := by
      simp [hz]
    rw [hform] at h49
    have h8253 : (-8253 : k) ≠ 0 := by norm_num
    exact hvne ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
      ((mul_eq_zero.mp h49).resolve_left h8253))
  have hscale :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            (5 / 243 : k) * B.leadingCoeff ^ 4 =
        (5 / 6561 : k) * (7 * u ^ 2 - 126 * u * v + 27 * v ^ 2) := by
    simp only [u, v]
    ring
  intro hz
  rw [hscale] at hz
  have h5 : (5 / 6561 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  exact hne ((mul_eq_zero.mp hz).resolve_left h5)

theorem lambdaHighBTieCombined610_natDegree_eq_of_coeff_ne
    {A B : k[X]}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (htie : 3 * A.natDegree = 2 * B.natDegree)
    (hcoeff :
      (35 / 6561 : k) * A.leadingCoeff ^ 6 -
          (70 / 729 : k) * (A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2) +
            (5 / 243 : k) * B.leadingCoeff ^ 4 ≠
        0) :
    (lambdaHighBTieCombined610 A B).natDegree = 4 * B.natDegree := by
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hdeg6 : 6 * A.natDegree = 4 * B.natDegree := by omega
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hB),
      natDegree_pow, natDegree_pow]
    omega
  have htop :
      (lambdaHighBTieCombined610 A B).coeff (4 * B.natDegree) ≠ 0 := by
    simp only [lambdaHighBTieCombined610, coeff_add, coeff_sub, coeff_smul,
      smul_eq_mul]
    have h1 : (A ^ 6).coeff (4 * B.natDegree) = A.leadingCoeff ^ 6 := by
      rw [← hdeg6, ← hA6, coeff_natDegree, leadingCoeff_pow]
    have h2 : (A ^ 3 * B ^ 2).coeff (4 * B.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
      rw [← hA3B2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
    have h3 : (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 := by
      rw [← hB4, coeff_natDegree, leadingCoeff_pow]
    simpa [h1, h2, h3] using hcoeff
  have hle :
      (lambdaHighBTieCombined610 A B).natDegree ≤ 4 * B.natDegree := by
    simp only [lambdaHighBTieCombined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_smul_le610 _ _).trans (hA6.symm ▸ hdeg6.le)
      · exact (natDegree_smul_le610 _ _).trans hA3B2.le
    · exact (natDegree_smul_le610 _ _).trans hB4.le
  exact natDegree_eq_of_le_of_coeff_ne_zero hle htop

/-- On the unique-`B` tie, a dropped `λ` combination cannot occur together
with a dropped `κ` companion. -/
theorem kappa_highBTie_impossible_of_lambda_drop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0)
    (hlamDrop :
      (lambdaHighBTieCombined610 A B).natDegree < 4 * B.natDegree)
    (hkapDeg :
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hBpos : 0 < B.natDegree := hcone.1.1
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    have hA : A.natDegree < B.natDegree := hcone.1.2.1
    omega
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  by_cases hdrop :
      (7 : k) * A.leadingCoeff ^ 3 - 12 * B.leadingCoeff ^ 2 = 0
  · have hrel : (7 : k) * A.leadingCoeff ^ 3 =
        12 * B.leadingCoeff ^ 2 := by linear_combination hdrop
    have hlamNe :=
      lambdaHighBTie_coeff_ne_zero_of_kappa_factor hAne hBne htie hrel
    have hcombdeg :=
      lambdaHighBTieCombined610_natDegree_eq_of_coeff_ne hAne hBne htie
        hlamNe
    exact (Nat.not_lt.mpr (le_of_eq hcombdeg.symm)) hlamDrop
  · have hA4B :
        (A ^ 4 * B).natDegree = 4 * A.natDegree + B.natDegree := by
      rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow]
    have hAB3 :
        (A * B ^ 3).natDegree = 4 * A.natDegree + B.natDegree := by
      rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
      omega
    have htop :
        (kappaHighBTieExpanded610 A B).coeff
            (4 * A.natDegree + B.natDegree) ≠
          0 := by
      simp only [kappaHighBTieExpanded610, coeff_add, coeff_smul,
        smul_eq_mul]
      have h1 : (A ^ 4 * B).coeff (4 * A.natDegree + B.natDegree) =
          A.leadingCoeff ^ 4 * B.leadingCoeff := by
        rw [← hA4B, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      have h2 : (A * B ^ 3).coeff (4 * A.natDegree + B.natDegree) =
          A.leadingCoeff * B.leadingCoeff ^ 3 := by
        rw [← hAB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
      simp only [h1, h2]
      have h35 : (-(35 / 729 : k)) ≠ 0 := by
        have : (35 / 729 : k) ≠ 0 :=
          div_ne_zero (by norm_num) (by norm_num)
        intro h0
        exact this (neg_eq_zero.mp h0)
      have h20 : (20 / 243 : k) ≠ 0 :=
        div_ne_zero (by norm_num) (by norm_num)
      -- Combined leading form is (-5/729) a b (7 a³ - 12 b²).
      have :
          (-(35 / 729 : k)) * (A.leadingCoeff ^ 4 * B.leadingCoeff) +
              (20 / 243 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) =
            (-(5 / 729 : k)) * A.leadingCoeff * B.leadingCoeff *
              (7 * A.leadingCoeff ^ 3 - 12 * B.leadingCoeff ^ 2) := by
        ring
      rw [this]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by
              have : (5 / 729 : k) ≠ 0 :=
                div_ne_zero (by norm_num) (by norm_num)
              intro h0
              exact this (neg_eq_zero.mp h0))
            (leadingCoeff_ne_zero.mpr hAne))
          (leadingCoeff_ne_zero.mpr hBne))
        hdrop
    have hle :
        (kappaHighBTieExpanded610 A B).natDegree ≤
          4 * A.natDegree + B.natDegree := by
      simp only [kappaHighBTieExpanded610]
      exact (natDegree_add_le _ _).trans
        (max_le ((natDegree_smul_le610 _ _).trans hA4B.le)
          ((natDegree_smul_le610 _ _).trans hAB3.le))
    have hcombdeg :
        (kappaHighBTieExpanded610 A B).natDegree =
          4 * A.natDegree + B.natDegree :=
      natDegree_eq_of_le_of_coeff_ne_zero hle htop
    have hrest :=
      degreeZeroKappaNoHighBTieRest610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C0 D0 E0 hcone
    have hsum :=
      degreeZeroKappaPolynomial610_eq_highBTie_add_rest l alpha beta
        delta epsilon zeta eta theta A B C0 D0 E0
    rw [hsum, natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hkapDeg
    omega

end UniqueBKappa610

/-! ## Weighted unique `λ` faces beyond the parent cones -/

section WeightedLambda610

variable {k : Type*} [Field k] [CharZero k]

/-- Unique weighted `A⁶` face, allowing some letters to outrank `A` in
ordinary degree so long as they stay below `6 deg A` in the four-face
weights, and so long as the load-free `D₀` monomials stay strictly
lighter. -/
def WeightedALeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    4 * B.natDegree < 6 * A.natDegree ∧
    3 * C0.natDegree < 6 * A.natDegree ∧
    2 * E0.natDegree < 6 * A.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 6 * A.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 6 * A.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 6 * A.natDegree

def WeightedBLeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < B.natDegree ∧
    6 * A.natDegree < 4 * B.natDegree ∧
    3 * C0.natDegree < 4 * B.natDegree ∧
    2 * E0.natDegree < 4 * B.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 4 * B.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 4 * B.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 4 * B.natDegree

def WeightedC0LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < C0.natDegree ∧
    6 * A.natDegree < 3 * C0.natDegree ∧
    4 * B.natDegree < 3 * C0.natDegree ∧
    2 * E0.natDegree < 3 * C0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 3 * C0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 3 * C0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 3 * C0.natDegree

def WeightedE0LeadsCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < E0.natDegree ∧
    6 * A.natDegree < 2 * E0.natDegree ∧
    4 * B.natDegree < 2 * E0.natDegree ∧
    3 * C0.natDegree < 2 * E0.natDegree ∧
    A.natDegree + 2 * D0.natDegree < 2 * E0.natDegree ∧
    2 * A.natDegree + B.natDegree + D0.natDegree < 2 * E0.natDegree ∧
    B.natDegree + C0.natDegree + D0.natDegree < 2 * E0.natDegree

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoA6_natDegree_lt_of_weighted_A
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedALeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoA6Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoA6Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoB4_natDegree_lt_of_weighted_B
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedBLeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoB4Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hA, hC, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoB4Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoC03_natDegree_lt_of_weighted_C0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedC0LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoC03Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hCpos, hA, hB, hE, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoC03Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaNoE02_natDegree_lt_of_weighted_E0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedE0LeadsCone610 A B C0 D0 E0) :
    (degreeZeroLambdaNoE02Polynomial610 l alpha beta delta epsilon zeta
        eta theta A B C0 D0 E0).natDegree <
      2 * E0.natDegree := by
  rcases hcone with ⟨hEpos, hA, hB, hC, hD1, hD2, hD3⟩
  simp only [degreeZeroLambdaNoE02Polynomial610, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow_two_km, zero_pow_three_km,
    zero_pow_four_km, zero_pow_five_km]
  compute_degree
  omega

theorem lambda_A6_impossible_of_weighted_A
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedALeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (35 / 6561 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((35 / 6561 : k) • A ^ 6).natDegree = 6 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoA6_natDegree_lt_of_weighted_A l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

theorem lambda_B4_impossible_of_weighted_B
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedBLeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hc : (5 / 243 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead : ((5 / 243 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoB4_natDegree_lt_of_weighted_B l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, _⟩
  omega

theorem lambda_C03_impossible_of_weighted_C0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedC0LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 81 : k)) ≠ 0 := by
    have : (5 / 81 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    intro h0
    exact this (neg_eq_zero.mp h0)
  have hlead :
      ((-(5 / 81 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoC03_natDegree_lt_of_weighted_C0 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, _⟩
  omega

theorem lambda_E02_impossible_of_weighted_E0
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : WeightedE0LeadsCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    False := by
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (5 / 9 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead : ((5 / 9 : k) • E0 ^ 2).natDegree = 2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroLambdaNoE02_natDegree_lt_of_weighted_E0 l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroLambdaPolynomial610_eq_E02_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, _⟩
  omega

end WeightedLambda610

/-! ## Closed faces and remaining residual -/

section ClosedFaces610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem HighBTieCone610_lambda_drop
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : HighBTieCone610 A B C0 D0 E0)
    (hdeg :
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0) :
    (lambdaHighBTieCombined610 A B).natDegree < 4 * B.natDegree := by
  by_contra h
  have hge : 4 * B.natDegree ≤
      (lambdaHighBTieCombined610 A B).natDegree := Nat.not_lt.mp h
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    have := hcone.2
    have := hcone.1.1
    omega
  have hBne : B ≠ 0 := by
    intro hB0
    have := hcone.1.1
    simp [hB0] at this
  have htie : 3 * A.natDegree = 2 * B.natDegree := hcone.2
  have hA6 : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow A 6
  have hB4 : (B ^ 4).natDegree = 4 * B.natDegree := natDegree_pow B 4
  have hA3B2 :
      (A ^ 3 * B ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne),
      natDegree_pow, natDegree_pow]
    omega
  have hle :
      (lambdaHighBTieCombined610 A B).natDegree ≤ 4 * B.natDegree := by
    simp only [lambdaHighBTieCombined610]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · have hdeg6 : 6 * A.natDegree = 4 * B.natDegree := by omega
        exact (natDegree_smul_le610 _ _).trans (hA6.symm ▸ hdeg6.le)
      · exact (natDegree_smul_le610 _ _).trans hA3B2.le
    · exact (natDegree_smul_le610 _ _).trans hB4.le
  have heq : (lambdaHighBTieCombined610 A B).natDegree =
      4 * B.natDegree := le_antisymm hle hge
  exact lambda_highBTie_impossible_of_combined_degree l alpha beta delta
    epsilon zeta eta theta A B C0 D0 E0 hcone heq hdeg

/-- Source-facing packet: `κ, λ, μ, ο` are ground constants, every unique
weighted `λ` face (including those beyond the parent AMaximal / BLeads /
C0Leads / E0Leads cones) is empty, and the unique-`B` tie is empty even
after the `λ` combination drops.  Remaining cones are the ratio-ties of
two or more of `{6 deg A, 4 deg B, 3 deg C₀, 2 deg E₀}` with dropped
load-free combination, and unique-high `D₀` with another letter
nonconstant.  The unused integrals `μ` and `ο` are the next comparison
on those leftover chambers. -/
theorem normalized610ScaleZero_kappaMuFaces_closed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        Polynomial.C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cLam ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cKap ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cMu ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0 =
        Polynomial.C cOmi ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ AMaximalCone610 A B C0 D0 E0 ∧
      ¬ BLeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ C0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ E0LeadsWeightedCone610 A B C0 D0 E0 ∧
      ¬ HighBTieCone610 A B C0 D0 E0 ∧
      ¬ WeightedALeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedBLeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedC0LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedE0LeadsCone610 A B C0 D0 E0 ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hdeg, hcLam, hlamDeg, hcKap, hkapDeg,
      hcMu, hmuDeg, hcOmi, homiDeg⟩ :=
    normalized610ScaleZero_firstIntegrals_eq_C hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hdeg, hcLam, hlamDeg, hcKap, hkapDeg, hcMu,
    hmuDeg, hcOmi, homiDeg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro hAmax
    exact lambda_A6_impossible_of_A_maximal l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hAmax hlamDeg
  · intro hBleads
    exact lambda_B4_impossible_of_B_leads l alpha beta delta epsilon zeta
      eta theta A B C0 D0 E0 hBleads hlamDeg
  · intro hCleads
    exact lambda_C03_impossible_of_C0_leads l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hCleads hlamDeg
  · intro hEleads
    exact lambda_E02_impossible_of_E0_leads l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hEleads hlamDeg
  · intro hBtie
    have hdrop :=
      HighBTieCone610_lambda_drop l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 hBtie hlamDeg
    exact kappa_highBTie_impossible_of_lambda_drop l alpha beta delta
      epsilon zeta eta theta A B C0 D0 E0 hBtie hdrop hkapDeg
  · intro hWA
    exact lambda_A6_impossible_of_weighted_A l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWA hlamDeg
  · intro hWB
    exact lambda_B4_impossible_of_weighted_B l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWB hlamDeg
  · intro hWC
    exact lambda_C03_impossible_of_weighted_C0 l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWC hlamDeg
  · intro hWE
    exact lambda_E02_impossible_of_weighted_E0 l alpha beta delta epsilon
      zeta eta theta A B C0 D0 E0 hWE hlamDeg
  · intro hExt
    exact extremeHighB_impossible l alpha beta delta epsilon zeta eta
      theta (j / t) A B C0 D0 E0 hjdiv hExt hder
  · intro hA6B
    exact uniqueHighB_impossible_of_A6B_leads l alpha beta delta epsilon
      zeta eta theta (j / t) A B C0 D0 E0 hjdiv hA6B hder
  · intro hDonly
    exact uniqueNonconstantD0_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hDonly.1 hDonly.2.1
      hDonly.2.2.1 hDonly.2.2.2.1 hDonly.2.2.2.2 hder
  · intro hBonly
    exact uniqueNonconstantB_impossible l alpha beta delta epsilon zeta
      eta theta (j / t) A B C0 D0 E0 hjdiv hBonly.1 hBonly.2.1
      hBonly.2.2.1 hBonly.2.2.2.1 hBonly.2.2.2.2 hder
  · intro hconst
    exact degreeZeroPrimitivePolynomial610_false_of_constant_core l alpha
      beta delta epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv
      hconst.1 hconst.2.1 hconst.2.2.1 hconst.2.2.2.1 hconst.2.2.2.2 hder

/-- Remaining cones after `κ` closes the unique-`B` drop and the broader
unique weighted `λ` faces are empty.  Next unused data: `μ` and `ο` on
the ratio-ties `A`–`C₀`, `A`–`E₀`, `B`–`C₀`, `B`–`E₀`, `C₀`–`E₀` and on
unique-high `D₀` with another letter nonconstant. -/
theorem normalized610ScaleZero_coneKappaMuResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree =
        0 ∧
      ¬ HighBTieCone610 A B C0 D0 E0 ∧
      ¬ WeightedALeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedBLeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedC0LeadsCone610 A B C0 D0 E0 ∧
      ¬ WeightedE0LeadsCone610 A B C0 D0 E0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hdeg, hcLam, hlamDeg, hcKap, hkapDeg,
      hcMu, hmuDeg, hcOmi, homiDeg, _hAmax, _hBleads, _hCleads, _hEleads,
      hBtie, hWA, hWB, hWC, hWE, _hExt, _hA6B, _hDonly, _hBonly,
      _hconst⟩ :=
    normalized610ScaleZero_kappaMuFaces_closed hsource
  exact ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0, ht,
    hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hBtie, hWA,
    hWB, hWC, hWE⟩

end ClosedFaces610

