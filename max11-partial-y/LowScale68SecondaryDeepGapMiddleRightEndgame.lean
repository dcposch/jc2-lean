import LowScale68SecondaryDeepGapMiddleBetaNextOrder

/-! # First-deep residual right/balanced middle after `beta = 0`

The next-order endgame leaves `n < g`, `2g < 3n`, middle `h < 2g` and
`3g ≤ 2h` with `beta = 0`.  After `beta = 0` one has `Q.natDegree ≤ 4n`,
so the Q-feed sits at `≤ 6n-1`, strictly below the cubic index
`11n-3g-1` on the whole first-deep window `g < 3n/2`.

* Right `3g < 2h < 4g`: ordinary `d e` is below the cubic.  Residual
  row-two at `11n-3g-1` is the `B,c` core
  `(32/81)*(11n-3g)*a*b^3`.
* Balanced `2h = 3g`: the `d e` face coincides with the cubic.  Residual
  row-two is `(-8/27)*(11n-3g)*(4 b c^2 - 9 d e)`.  Vanishing plus
  ordinary I4/I3 feeds residual row-one at `12n-3g-1`, whose scalar is
  `(-64/9)*(4n-g)*c^3`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DeepGapMiddleRightEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Q-feed strictly below the cubic index -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_Q_degree_lt_cubic_of_firstDeep_beta
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n) :
    (A * derivative (residualIncidenceQ68 B c d e)).natDegree <
        11 * n - 3 * g - 1 ∧
      (derivative A * residualIncidenceQ68 B c d e).natDegree <
        11 * n - 3 * g - 1 := by
  have h1 := middleBeta_natDegree_mul_derivative_le68 A
    (residualIncidenceQ68 B c d e) (2 * n) (4 * n) hA (by omega) hQ
  have h2 := middleBeta_natDegree_derivative_mul_le68 A
    (residualIncidenceQ68 B c d e) (2 * n) (4 * n) (by omega) hA hQ
  have hi : 2 * n + 4 * n - 1 = 6 * n - 1 := by omega
  have hle1 : (A * derivative (residualIncidenceQ68 B c d e)).natDegree ≤
      6 * n - 1 := by simpa only [hi] using h1
  have hle2 : (derivative A * residualIncidenceQ68 B c d e).natDegree ≤
      6 * n - 1 := by simpa only [hi] using h2
  have hlt : 6 * n - 1 < 11 * n - 3 * g - 1 := by omega
  exact ⟨hle1.trans_lt hlt, hle2.trans_lt hlt⟩

/-! ## Right chamber `3g < 2h`: cubic `B,c` core at `11n-3g-1` -/

set_option maxHeartbeats 8000000 in
theorem residualRowTwo_coeff_rightChamber_of_firstDeep_beta
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hQdeg := residualRowTwoInner_Q_degree_lt_cubic_of_firstDeep_beta
    A B c d e n g hn hgt hrel hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualRowTwoInner_Bd_degree_le68_of_firstDeep B d n g h
    hg hgh hh hrel hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hde := residualRowTwoInner_de_degree_le68_of_firstDeep d e n g h
    hg hgh hh hrel hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, h0de, hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

theorem residualRowTwo_rightChamber_ne_zero_of_firstDeep_beta
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (ha0 : A.coeff (2 * n) ≠ 0)
    (hb0 : B.coeff (3 * n - g) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_rightChamber_of_firstDeep_beta A B c d e n g h
    hn hg hgh hh hgt hrel hright hA hB hc hd he hQ hdisc]
  have hscalar : (32 / 81 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero hscalar hN) ha0) (pow_ne_zero 3 hb0)

/-! ## Balanced wall `2h = 3g`: cubic plus `d e` -/

set_option maxHeartbeats 8000000 in
theorem residualRowTwo_coeff_balancedChamber_of_firstDeep_beta
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) *
        ((4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hface : 11 * n - 2 * h = 11 * n - 3 * g := by omega
  have hQdeg := residualRowTwoInner_Q_degree_lt_cubic_of_firstDeep_beta
    A B c d e n g hn hgt hrel hA hQ
  have hAQ : (A * derivative Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.1
  have hAQ' : (derivative A * Q).natDegree < idx := by
    dsimp [idx]
    exact hQdeg.2
  have hBd := residualRowTwoInner_Bd_degree_le68_of_firstDeep B d n g h
    hg hgh hh hrel hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    have hidx_de : 11 * n - 2 * h - 1 = idx := by
      dsimp [idx]
      omega
    rw [← hidx_de, hde, hface]
  have hcore :
      ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
        ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
        ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    rw [hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  have hinner : inner.coeff idx =
      (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
      (-18 : k) * ((11 * n - 3 * g : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0Bd, hde']
    linear_combination hcore
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  exact residualBalancedRowTwoScalar68
    ((11 * n - 3 * g : ℕ) : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hdisc

theorem residualRowTwo_balanced_forces_relation_of_firstDeep_beta
    (A B c d e load : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 4 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hload : load.natDegree < 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hsum
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload, add_zero,
    residualRowTwo_coeff_balancedChamber_of_firstDeep_beta A B c d e n g h
      hn hg hgh hh hgt hrel hbalanced hA hB hc hd he hQ hdisc] at hcoeff
  have hsc : (-8 / 27 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hcoeff).resolve_left (mul_ne_zero hsc hN)

/-! ## Balanced residual row-one at `12n-3g-1` -/

set_option maxHeartbeats 8000000 in
theorem residualRowOne_coeff_balancedChamber_of_firstDeep
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
            ((12 * n - 3 * g : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hI3low : (A * derivative I3).natDegree < idx := by
    have h := middleBeta_natDegree_mul_derivative_le68 A I3
      (2 * n) (7 * n - g) hA (by omega) hI3
    have hi : 2 * n + (7 * n - g) - 1 = 9 * n - g - 1 := by omega
    have hle : (A * derivative I3).natDegree ≤ 9 * n - g - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt (by
      dsimp [idx]
      omega)
  have hd2deg : (d ^ 2).natDegree ≤ 10 * n - 3 * g := by
    compute_degree
    omega
  have hd2 : (d ^ 2).coeff (10 * n - 3 * g) =
      d.coeff (5 * n - h) ^ 2 := by
    have hd2pow := coeff_pow_at_bound68 d (5 * n - h) 2 hd
    have hi : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
    simpa only [hi] using hd2pow
  have hAd2coeff := coeff_mul_at_bounds68 A (d ^ 2) (2 * n) (10 * n - 3 * g)
    hA hd2deg
  have hiAd2 : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
  rw [hiAd2, hd2] at hAd2coeff
  have hAd2der := coeff_derivative_at_bound68 (A * d ^ 2)
    (12 * n - 3 * g) (by omega)
  rw [hAd2coeff] at hAd2der
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hB2pow := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hB2pow
  have hAB2ccoeff := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (6 * n - 2 * g) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + (6 * n - 2 * g) + (4 * n - g) = 12 * n - 3 * g :=
    by omega
  rw [hiAB2c, hB2] at hAB2ccoeff
  have hAB2cder := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2ccoeff] at hAB2cder
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by omega
  rw [hiee] at hee
  have hidx_ee : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]; omega
  have hlowFace : 12 * n - 2 * g - h - 1 < idx := by
    dsimp [idx]
    omega
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
      natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hd
    have hsum : (3 * n - g) + (4 * n - g) + (5 * n - h) =
        12 * n - 2 * g - h := by omega
    rw [hsum] at hprod
    exact ((natDegree_derivative_le (B * c * d)).trans (by omega)).trans_lt
      hlowFace
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hcd : (c * d).natDegree ≤ (4 * n - g) + (5 * n - h) :=
      natDegree_mul_le_of_le hc hd
    have hprod := natDegree_mul_le_of_le hdB hcd
    have hsum : (3 * n - g - 1) + ((4 * n - g) + (5 * n - h)) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (derivative B * (c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    have hassoc : derivative B * (c * d) = derivative B * c * d := by ring
    rw [hassoc] at hle
    exact hle.trans_lt hlowFace
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le hB2deg hde
    have hsum : (6 * n - 2 * g) + (6 * n - h - 1) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (B ^ 2 * derivative e).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    exact hle.trans_lt hlowFace
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hAd2sm : ((3 : k) • derivative (A * d ^ 2)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
        ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAd2der]
  have hAB2csm : ((-2 : k) • derivative (A * B ^ 2 * c)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAB2cder]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * (c.coeff (4 * n - g) ^ 2 * c.coeff (4 * n - g) *
        ((4 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hc3]
  have heesm : ((-18 : k) • (e * derivative e)).coeff idx =
      (-18 : k) * (e.coeff (6 * n - h) ^ 2 * ((6 * n - h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, ← hidx_ee, hee]
    ring
  have hinner : (residualRowOneInner68 A B c d e).coeff idx =
      A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, hAd2sm, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, heesm]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_balancedChamber_eq_of_firstDeep
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hface2 : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-64 / 9 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 := by
  rw [residualRowOne_coeff_balancedChamber_of_firstDeep A B c d e n g h
    hn hg hgh hh hgt hrel hbalanced hA hB hcdeg hd he hI3]
  have hcast12 : (((12 * n - 3 * g : ℕ) : k)) =
      (12 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - h : ℕ) : k)) =
      (6 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 6 * n)]
    push_cast
    rfl
  have hbal : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    have := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at this
    exact this
  rw [hcast12, hcast4, hcast6]
  exact residualRowOneScalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hface2

theorem residualRowOne_balanced_coeff_ne_zero_of_firstDeep
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hgt : n < g) (hrel : 2 * g < 3 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      7 * n - g)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hface2 : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowOne_coeff_balancedChamber_eq_of_firstDeep A B c d e n g h
    hn hg hgh hh hgt hrel hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hface2]
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  rw [hcast4]
  have hNG : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    rw [← hcast4]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact residualRowOneScalar_ne_zero68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hNG
    (by
      have := congrArg (fun m : ℕ => (m : k)) hbalanced
      push_cast at this
      exact this)
    hdisc hinc hface2

/-! ## Shared reconstruction for the remaining packet -/

theorem deepGapFirstMiddle_four_of_beta
    (n g h : ℕ) (a b c dh eh d2 e2 beta : k)
    (hh : h < 2 * g)
    (hinv : DeepGapResidualInvariants68 n g h a b c dh eh d2 e2 beta)
    (hbeta : beta = 0) :
    b * eh + c * dh = 0 := by
  rcases lt_trichotomy (g + h) (3 * n) with hlt | heq | hgt'
  · exact hinv.four_middle_below hh hlt
  · have hmix := hinv.four_middle_mixed hh heq
    rw [hbeta] at hmix
    have h8 : (8 / 3 : k) ≠ 0 := by norm_num
    have : (8 / 3 : k) * (b * eh + c * dh) = 0 := by
      simpa [mul_zero, add_zero] using hmix
    exact (mul_eq_zero.mp this).resolve_left h8
  · exact (hinv.four_middle_above hh hgt').2

/-! ## Canonical right/balanced theorems -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleRight_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n)
    (hright :
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
      h < 2 * g ∧ 3 * g < 2 * h) :
    False := by
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
  change n < g ∧ 2 * g < 3 * n at hchamber
  change h < 2 * g ∧ 3 * g < 2 * h at hright
  have hnext :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleNext_obstruction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  have hbeta : beta = 0 := hnext.2.2
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  have hl : l = 0 := hsel.1
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hgh : g < h := hsel.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := hsel.2.2.2.2.2.1
  have hee : ee.natDegree ≤ 6 * n - h := hsel.2.2.2.2.2.2.1
  have he' : ee.natDegree ≤ 6 * n - g := (hsel.2.2.2.1).le
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hinc := deepGapFirstMiddle_four_of_beta n g h
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
    (d.coeff (5 * n - 2 * g)) (ee.coeff (6 * n - 2 * g)) beta
    hright.1 hsel.2.2.2.2.2.2.2 hbeta
  have hface : SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
      (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) :=
    ⟨hinc, hsel.2.2.2.2.2.2.2.three_middle hright.1⟩
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    intro hz
    have hzgap : secondaryResidualGap68 n d ee = 6 * n + 1 := by
      simp [secondaryResidualGap68, polynomialGap68, hz.1, hz.2]
    have : h = 6 * n + 1 := by
      simpa only [h, d, ee, n] using hzgap
    omega
  have hattained :
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 :=
    secondaryResidualGap68_boundary_attained n d ee
      (hd.trans_lt (by omega)) (hee.trans_lt (by omega)) hnotboth
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) ha hsel.2.1 hattained hface
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl, hbeta] at hi4c
  have hQle := residualIncidenceQ68_degree_le_fourRadius_of_beta
    gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hchamber.1 hchamber.2
    hA hB hc (hd.trans (by omega)) he' hi4c
  have hrowTwoe : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo : secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have h := hrowTwoe
    rw [hCrec, hDrec, hErec] at h
    exact polynomialSecondaryResidualRowTwo68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h
  rw [hl, hbeta] at hrowTwo
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hload :
      (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1 :=
    cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstDeep_beta
      alpha gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg0 hchamber.1 hchamber.2
      hA hB hc hD' he'
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    (11 * n - 3 * g - 1) hload hrowTwo
  exact residualRowTwo_rightChamber_ne_zero_of_firstDeep_beta Ae Be ce d ee
    n g h hn hg0 hgh hright.1 hchamber.1 hchamber.2 hright.2
    hA hB hc hd hee hQle hclass.2.2.2.2 ha hclass.1 hcoeff0

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleBalanced_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n)
    (hbalanced :
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
      h < 2 * g ∧ 2 * h = 3 * g) :
    False := by
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
  change n < g ∧ 2 * g < 3 * n at hchamber
  change h < 2 * g ∧ 2 * h = 3 * g at hbalanced
  have hnext :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleNext_obstruction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  have hbeta : beta = 0 := hnext.2.2
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  have hl : l = 0 := hsel.1
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hgh : g < h := hsel.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := hsel.2.2.2.2.2.1
  have hee : ee.natDegree ≤ 6 * n - h := hsel.2.2.2.2.2.2.1
  have he' : ee.natDegree ≤ 6 * n - g := (hsel.2.2.2.1).le
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hinc := deepGapFirstMiddle_four_of_beta n g h
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
    (d.coeff (5 * n - 2 * g)) (ee.coeff (6 * n - 2 * g)) beta
    hbalanced.1 hsel.2.2.2.2.2.2.2 hbeta
  have hface : SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
      (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) :=
    ⟨hinc, hsel.2.2.2.2.2.2.2.three_middle hbalanced.1⟩
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    intro hz
    have hzgap : secondaryResidualGap68 n d ee = 6 * n + 1 := by
      simp [secondaryResidualGap68, polynomialGap68, hz.1, hz.2]
    have : h = 6 * n + 1 := by
      simpa only [h, d, ee, n] using hzgap
    omega
  have hattained :
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 :=
    secondaryResidualGap68_boundary_attained n d ee
      (hd.trans_lt (by omega)) (hee.trans_lt (by omega)) hnotboth
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h)) ha hsel.2.1 hattained hface
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl, hbeta] at hi4c
  have hQle := residualIncidenceQ68_degree_le_fourRadius_of_beta
    gamma delta epsilon zeta i4 Ae Be ce d ee n g hn hchamber.1 hchamber.2
    hA hB hc (hd.trans (by omega)) he' hi4c
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  have hI3le :=
    secondaryResidualInvariantThreePolynomial68_degree_le_of_firstDeep
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g hn hchamber.1
      hchamber.2 hA hB hc (hd.trans (by omega)) he' hi3c
  have hrowTwoe : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo : secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have h := hrowTwoe
    rw [hCrec, hDrec, hErec] at h
    exact polynomialSecondaryResidualRowTwo68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h
  rw [hl, hbeta] at hrowTwo
  have hD' : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g :=
    middleBeta_natDegree_translatedD_le68 Ae Be d n g h
      hn hgh hchamber.2 hA hB hd
  have hload2 :
      (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          11 * n - 3 * g - 1 :=
    cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstDeep_beta
      alpha gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg0 hchamber.1 hchamber.2
      hA hB hc hD' he'
  have hrel := residualRowTwo_balanced_forces_relation_of_firstDeep_beta
    Ae Be ce d ee
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
    n g h hn hg0 hgh hbalanced.1 hchamber.1 hchamber.2 hbalanced.2
    hA hB hc hd hee hQle hclass.2.2.2.2 hload2 hrowTwo
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowOne : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have h := h1e
    rw [hCrec, hDrec, hErec] at h
    exact polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h
  rw [hl] at hrowOne
  have hload1 :
      (cubicLoadRowOnePolynomial68 0 alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee).natDegree <
          12 * n - 3 * g - 1 :=
    cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstDeep
      0 alpha beta gamma delta epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg0 rfl hchamber.2
      hA hB hc hD' he'
  have hcoeff0 := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [coeff_add, coeff_zero,
    coeff_eq_zero_of_natDegree_lt hload1, add_zero] at hcoeff0
  exact residualRowOne_balanced_coeff_ne_zero_of_firstDeep Ae Be ce d ee
    n g h hn hg0 hgh hbalanced.1 hchamber.1 hchamber.2 hbalanced.2
    hA hB hc hd hee hI3le hclass.2.1 hclass.2.2.2.2 hinc hrel hcoeff0

/-- On the first-deep chamber `n < g < 3n/2`, residual middle right and
balanced windows are impossible.  Combined with the next-order left and
`2h=3n` closures, the whole first-deep packet is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirst_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n) :
    False := by
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
  change n < g ∧ 2 * g < 3 * n at hchamber
  have hnext :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleNext_obstruction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
  have hh : h < 2 * g := hnext.1
  have hge : 3 * g ≤ 2 * h := hnext.2.1
  rcases lt_trichotomy (2 * h) (3 * g) with hlt | heq | hgt
  · exact (not_lt.mpr hge) hlt
  · exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleBalanced_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh heq)
  · exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMiddleRight_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        And.intro hh hgt)

end DeepGapMiddleRightEndgame68

end Max11DegreeRoutes
