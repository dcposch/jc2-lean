import LowScale68SecondaryResidualHalfRadiusLoadWall
import LowScale68SecondaryResidualRowTwoLoadDominance

/-! # Mixed residual half-radius wall `n = 3g`, `2h = n`

The tracked module closes `2g < n < 3g` with `2h = n` by the left
`d e` faces plus the Jacobian cores.  On the remaining wall `n = 3g`
one also has `2h = 3g`, so the cubic `B,c` core and the I4-forced
`Q`-feed meet the same indices `10n-1` and `12n-1`.  The corrected
mixed scalars still force `l = 0`; the tracked load-zero endgame then
closes the canonical `2g < n` branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem residualHalfRadiusBoundary_twoGap
    (n g : ℕ) (hg : 0 < g) (hwallg : n = 3 * g) : 2 * g < n := by
  omega

theorem residualHalfRadiusBoundary_gap_lt
    (n g h : ℕ) (hsmall : 2 * g < n) (hwallh : 2 * h = n) : g < h :=
  residualHalfRadiusLoadWall_gap_lt n g h hsmall hwallh

theorem residualHalfRadiusBoundary_lt_double
    (n g h : ℕ) (hg : 0 < g) (hwallg : n = 3 * g) (hwallh : 2 * h = n) :
    h < 2 * g :=
  residualHalfRadiusLoadWall_lt_double n g h hg (by omega) hwallh

theorem residualHalfRadiusBoundary_win
    (n g h : ℕ) (hsmall : 2 * g < n) (hwallh : 2 * h = n) : g + h < n :=
  residualHalfRadiusLoadWall_win n g h hsmall hwallh

theorem residualHalfRadiusBoundary_large
    (n g : ℕ) (hwallg : n = 3 * g) : n ≤ 3 * g := by
  omega

theorem residualHalfRadiusBoundary_twoIndex
    (n h : ℕ) (hwallh : 2 * h = n) :
    11 * n - 2 * h - 1 = 10 * n - 1 :=
  residualHalfRadiusLoadWall_twoIndex n h hwallh

theorem residualHalfRadiusBoundary_zeroIndex
    (n h : ℕ) (hwallh : 2 * h = n) :
    13 * n - 2 * h - 1 = 12 * n - 1 :=
  residualHalfRadiusLoadWall_zeroIndex n h hwallh

theorem residualHalfRadiusBoundary_cubicIndex
    (n g : ℕ) (hwallg : n = 3 * g) :
    11 * n - 3 * g - 1 = 10 * n - 1 := by
  omega

theorem residualHalfRadiusBoundary_cubicSum
    (n g : ℕ) (hwallg : n = 3 * g) : 11 * n - 3 * g = 10 * n := by
  omega

theorem residualHalfRadiusBoundary_B3Index
    (n g : ℕ) (hwallg : n = 3 * g) : 9 * n - 3 * g = 8 * n := by
  omega

theorem residualHalfRadiusBoundary_deIndex
    (n h : ℕ) (hwallh : 2 * h = n) : 11 * n - 2 * h = 10 * n :=
  residualHalfRadiusLoadWall_deIndex n h hwallh

theorem residualHalfRadiusBoundary_eBound
    (n g h : ℕ) {e : k[X]} (hgh : g < h)
    (he : e.natDegree ≤ 6 * n - h) :
    e.natDegree ≤ 6 * n - g :=
  he.trans (by omega)

theorem residualHalfRadiusBoundary_dBound
    (n g h : ℕ) {d : k[X]} (hgh : g < h)
    (hd : d.natDegree ≤ 5 * n - h) :
    d.natDegree ≤ 5 * n - g :=
  hd.trans (by omega)

theorem residualHalfRadiusBoundary_gap_cast
    (n g : ℕ) (hwallg : n = 3 * g) :
    (g : k) = (n : k) / 3 := by
  apply eq_div_of_mul_eq (by norm_num : (3 : k) ≠ 0)
  have h3 : (3 : k) * (g : k) = (n : k) := by
    rw [hwallg]
    push_cast
    ring
  rw [mul_comm]
  exact h3

theorem residualHalfRadiusBoundary_cast3
    (n g : ℕ) (hwallg : n = 3 * g) :
    ((3 * n - g : ℕ) : k) = (8 / 3 : k) * (n : k) := by
  subst hwallg
  have hsub : 3 * (3 * g) - g = 8 * g := by omega
  rw [hsub]
  push_cast
  ring

theorem residualHalfRadiusBoundary_cast11
    (n g : ℕ) (hwallg : n = 3 * g) :
    ((11 * n - 3 * g : ℕ) : k) = (10 : k) * (n : k) := by
  have heq : 11 * n - 3 * g = 10 * n :=
    residualHalfRadiusBoundary_cubicSum n g hwallg
  rw [heq]
  push_cast
  rfl

theorem residualHalfRadiusBoundary_cast10
    (n h : ℕ) (hwallh : 2 * h = n) :
    ((11 * n - 2 * h : ℕ) : k) = (10 : k) * (n : k) := by
  have heq : 11 * n - 2 * h = 10 * n :=
    residualHalfRadiusBoundary_deIndex n h hwallh
  rw [heq]
  push_cast
  rfl

theorem residualHalfRadiusBoundary_cast2 (n : ℕ) :
    ((2 * n : ℕ) : k) = (2 : k) * (n : k) := by
  push_cast
  rfl

theorem residualHalfRadiusBoundary_cast8 (n : ℕ) :
    ((8 * n : ℕ) : k) = (8 : k) * (n : k) := by
  push_cast
  rfl

/-! ## Mixed numerators

Row two / row zero at the collided index are the left `d e` faces, the
cubic `B,c` cores evaluated at `11n-3g = 10n`, the I4-forced `Q`-feed,
and the Jacobian cores.  `B^2 d` stays strictly below both load
indices. -/

/-- Mixed row-two scalar at index `10n-1`. -/
def residualHalfRadiusBoundaryTwoScalar68 (N a b c d e l : k) : k :=
  N * ((80 / 3 : k) * d * e +
    (80 / 81 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2) +
    (35 / 576 : k) * l * a ^ 5)

/-- Mixed row-zero scalar at index `12n-1`. -/
def residualHalfRadiusBoundaryZeroScalar68 (N a b c d e l : k) : k :=
  N * a * ((-8 / 9 : k) * d * e +
    (-8 / 243 : k) * b * (a * b ^ 2 - (9 : k) * c ^ 2) +
    (35 / 1728 : k) * l * a ^ 5)

/-- The cubic increment is parallel to `d e`; the open-strip combination
kills both homogeneous faces and leaves the combined load. -/
theorem residualHalfRadiusBoundary_two_zero_kill_hom
    (N a b c d e l : k) :
    (30 : k) * residualHalfRadiusBoundaryZeroScalar68 N a b c d e l +
        a * residualHalfRadiusBoundaryTwoScalar68 N a b c d e l =
      (385 / 576 : k) * N * l * a ^ 6 := by
  simp only [residualHalfRadiusBoundaryTwoScalar68,
    residualHalfRadiusBoundaryZeroScalar68]
  ring

theorem residualHalfRadiusBoundary_two_zero_force_l
    (N a b c d e l : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (htwo : residualHalfRadiusBoundaryTwoScalar68 N a b c d e l = 0)
    (hzero : residualHalfRadiusBoundaryZeroScalar68 N a b c d e l = 0) :
    l = 0 := by
  have hcomb := residualHalfRadiusBoundary_two_zero_kill_hom N a b c d e l
  rw [htwo, hzero, mul_zero, mul_zero, add_zero] at hcomb
  have h385 : (385 / 576 : k) ≠ 0 := by norm_num
  have hpre : (385 / 576 : k) * N * a ^ 6 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h385 hN) (pow_ne_zero 6 ha)
  have : (385 / 576 : k) * N * a ^ 6 * l = 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcomb.symm
  exact (mul_eq_zero.mp this).resolve_left hpre

/-! ## Row-zero incidence rewrite -/

/-- Inner expression of residual row zero after the `Q` rewrite, before
`4/27`. -/
def residualHalfRadiusBoundaryRowZeroInner68 (A B c d e : k[X]) : k[X] :=
  -(A * derivative A * residualIncidenceQ68 B c d e) -
    (1 / 9 : k) • (A * derivative A * B ^ 3) +
    derivative A * B * c ^ 2 -
    (3 : k) • (derivative A * d * e) -
    A * B ^ 2 * derivative d -
    A * B * derivative B * d +
    (3 : k) • (B * c * derivative e) -
    (3 : k) • (B * d * derivative d) -
    (3 : k) • (derivative B * d ^ 2) -
    (3 : k) • (c * derivative c * d)

set_option maxHeartbeats 8000000 in
theorem residualHalfRadiusBoundaryRowZero_eq_inner68 (A B c d e : k[X]) :
    secondaryResidualRowZeroPolynomial68 A B c d e =
      (4 / 27 : k) • residualHalfRadiusBoundaryRowZeroInner68 A B c d e := by
  simp only [secondaryResidualRowZeroPolynomial68,
    residualHalfRadiusBoundaryRowZeroInner68, residualIncidenceQ68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_smul, derivative_C, zero_mul, zero_add, smul_add, smul_sub,
    Polynomial.smul_eq_C_mul]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-! ## Homogeneous residual row two at `10n-1` -/

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowTwoPolynomial68_coeff_halfRadiusBoundary
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwallg : n = 3 * g) (hwallh : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (10 * n - 1) =
      (80 / 3 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        (80 / 81 : k) * (n : k) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) +
        (-245 / 5184 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 10 * n - 1
  have hsmall : 2 * g < n := residualHalfRadiusBoundary_twoGap n g hg hwallg
  have hgh : g < h := residualHalfRadiusBoundary_gap_lt n g h hsmall hwallh
  have hh : h < 2 * g :=
    residualHalfRadiusBoundary_lt_double n g h hg hwallg hwallh
  have he' : e.natDegree ≤ 6 * n - g :=
    residualHalfRadiusBoundary_eBound n g h hgh he
  have hd' : d.natDegree ≤ 5 * n - g :=
    residualHalfRadiusBoundary_dBound n g h hgh hd
  have hQdeg := residualIncidenceQ68_degree_le_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hg hsmall hA hB hc hd' he' hi4
  have hQ8 := residualIncidenceQ68_coeff_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hn hg hsmall hA hB hc hd' he' hi4
  have hAQ : (A * derivative Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (8 * n) * ((8 * n : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 A Q (2 * n) (8 * n)
      (by omega) hA hQdeg
    have hi : 2 * n + 8 * n - 1 = idx := by
      dsimp [idx]
      omega
    simpa only [hi] using h
  have hQA : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (8 * n) * ((2 * n : ℕ) : k) := by
    have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
      (natDegree_derivative_le A).trans (by omega)
    have h := coeff_mul_at_bounds68 (derivative A) Q (2 * n - 1) (8 * n)
      hdA hQdeg
    have hi : (2 * n - 1) + 8 * n = idx := by
      dsimp [idx]
      omega
    have hA' := coeff_derivative_at_bound68 A (2 * n) (by omega)
    rw [hi, hA'] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap
    B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
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
  have hBcpos : 0 < 11 * n - 3 * g := by omega
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) hBcpos
  rw [hBccoeff] at hBc
  have hBc' : (derivative (B * c ^ 2)).coeff idx =
      B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k) := by
    have hi : 11 * n - 3 * g - 1 = idx := by
      dsimp [idx]
      omega
    rwa [← hi]
  have hcast3 : ((3 * n - g : ℕ) : k) = (8 / 3 : k) * (n : k) :=
    residualHalfRadiusBoundary_cast3 n g hwallg
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) :=
    residualHalfRadiusBoundary_cast2 n
  have hcast11 : ((11 * n - 3 * g : ℕ) : k) = (10 : k) * (n : k) :=
    residualHalfRadiusBoundary_cast11 n g hwallg
  have hcast8 : ((8 * n : ℕ) : k) = (8 : k) * (n : k) :=
    residualHalfRadiusBoundary_cast8 n
  have hcast10 : ((11 * n - 2 * h : ℕ) : k) = (10 : k) * (n : k) :=
    residualHalfRadiusBoundary_cast10 n h hwallh
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have hQpart : ((-6 : k) • (A * derivative Q)).coeff idx +
      ((3 : k) • (derivative A * Q)).coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) := by
    rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, hAQ, hQA, hcast8,
      hcast2]
    ring
  have hcub : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
      ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
      ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (-20 / 3 : k) * (n : k) * B.coeff (3 * n - g) *
        (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
          (9 : k) * c.coeff (4 * n - g) ^ 2) := by
    rw [coeff_smul, coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hABpow, hA3']
    rw [hBc', hcast3, hcast2, hcast11]
    ring
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    have hidxde : 11 * n - 2 * h - 1 = idx := by
      dsimp [idx]
      omega
    rw [← hidxde, hde]
  have hinner : inner.coeff idx =
      (-42 : k) * (n : k) * A.coeff (2 * n) * Q.coeff (8 * n) +
        (-20 / 3 : k) * (n : k) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) +
        (-180 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Bd]
    have hde'' : ((-18 : k) • derivative (d * e)).coeff idx =
        (-180 : k) * (n : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
      rw [hde', hcast10]
      ring
    linear_combination hQpart + hcub + hde''
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  simp only [Q, hQ8]
  ring

/-! ## Homogeneous residual row zero at `12n-1` -/

set_option maxHeartbeats 8000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_halfRadiusBoundary
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwallg : n = 3 * g) (hwallh : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (12 * n - 1) =
      (-8 / 9 : k) * (n : k) * A.coeff (2 * n) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        -(8 / 243 : k) * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) *
          (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 -
            (9 : k) * c.coeff (4 * n - g) ^ 2) +
        (35 / 15552 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualHalfRadiusBoundaryRowZeroInner68 A B c d e
  set idx := 12 * n - 1
  have hsmall : 2 * g < n := residualHalfRadiusBoundary_twoGap n g hg hwallg
  have hgh : g < h := residualHalfRadiusBoundary_gap_lt n g h hsmall hwallh
  have he' : e.natDegree ≤ 6 * n - g :=
    residualHalfRadiusBoundary_eBound n g h hgh he
  have hd' : d.natDegree ≤ 5 * n - g :=
    residualHalfRadiusBoundary_dBound n g h hgh hd
  have hQdeg := residualIncidenceQ68_degree_le_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hg hsmall hA hB hc hd' he' hi4
  have hQ8 := residualIncidenceQ68_coeff_eightRadius_of_I4
    l beta gamma delta epsilon zeta i4 A B c d e n g
    hn hg hsmall hA hB hc hd' he' hi4
  have hAAQ := coeff_mul_mul_derivative_at_bounds68 A Q A
    (2 * n) (8 * n) (2 * n) (by omega) hA hQdeg hA
  have hiAAQ : 2 * n + 8 * n + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAAQ] at hAAQ
  have hAAQ' : (A * derivative A * Q).coeff idx =
      A.coeff (2 * n) ^ 2 * Q.coeff (8 * n) * ((2 * n : ℕ) : k) := by
    have hcomm : A * derivative A * Q = A * Q * derivative A := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm, pow_two] using hAAQ
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hAAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 3) A
    (2 * n) (9 * n - 3 * g) (2 * n) (by omega) hA hB3deg hA
  have hiAAB : 2 * n + (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAAB, hB3] at hAAB
  have hAAB' : (A * derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    have hcomm : A * derivative A * B ^ 3 =
        A * B ^ 3 * derivative A := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm, pow_two] using hAAB
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
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hABc := coeff_mul_at_bounds68 (derivative A) (B * c ^ 2)
    (2 * n - 1) (11 * n - 3 * g) hdA hBcdeg
  have hiABc : (2 * n - 1) + (11 * n - 3 * g) = idx := by
    dsimp [idx]
    omega
  have hA' := coeff_derivative_at_bound68 A (2 * n) (by omega)
  rw [hiABc, hA', hBccoeff] at hABc
  have hABc' : (derivative A * B * c ^ 2).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    have hcomm : derivative A * B * c ^ 2 =
        derivative A * (B * c ^ 2) := by
      simp only [mul_assoc]
    rw [hcomm]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hABc
  have hAde' : (derivative A * d * e).coeff idx =
      A.coeff (2 * n) * d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((2 * n : ℕ) : k) := by
    have hAd := coeff_mul_at_bounds68 (derivative A) d (2 * n - 1) (5 * n - h)
      hdA hd
    have hmul2 := coeff_mul_at_bounds68 (derivative A * d) e
      ((2 * n - 1) + (5 * n - h)) (6 * n - h)
      (natDegree_mul_le.trans (Nat.add_le_add hdA hd)) he
    have hi : (2 * n - 1) + (5 * n - h) + (6 * n - h) = idx := by
      dsimp [idx]
      omega
    rw [hi, hAd, hA'] at hmul2
    convert hmul2 using 1
    push_cast
    ring
  have hlow2 : (A * B ^ 2 * derivative d).natDegree < idx := by
    dsimp [idx]
    have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
      compute_degree
      omega
    have hdder : (derivative d).natDegree ≤ 5 * n - h - 1 :=
      (natDegree_derivative_le d).trans (by omega)
    have hAB2 := natDegree_mul_le_of_le hA hB2
    have hprod := natDegree_mul_le_of_le hAB2 hdder
    omega
  have hlow3 : (A * B * derivative B * d).natDegree < idx := by
    dsimp [idx]
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hAB := natDegree_mul_le_of_le hA hB
    have hAB' := natDegree_mul_le_of_le hAB hdB
    have hprod := natDegree_mul_le_of_le hAB' hd
    omega
  have hlow4 : (B * c * derivative e).natDegree < idx := by
    dsimp [idx]
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hBc := natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hde
    omega
  have hlow5 : (B * d * derivative d).natDegree < idx := by
    dsimp [idx]
    have hdder : (derivative d).natDegree ≤ 5 * n - h - 1 :=
      (natDegree_derivative_le d).trans (by omega)
    have hBd := natDegree_mul_le_of_le hB hd
    have hprod := natDegree_mul_le_of_le hBd hdder
    omega
  have hlow6 : (derivative B * d ^ 2).natDegree < idx := by
    dsimp [idx]
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hd2 : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
      compute_degree
      omega
    have hprod := natDegree_mul_le_of_le hdB hd2
    omega
  have hlow7 : (c * derivative c * d).natDegree < idx := by
    dsimp [idx]
    have hdc : (derivative c).natDegree ≤ 4 * n - g - 1 :=
      (natDegree_derivative_le c).trans (by omega)
    have hc' := natDegree_mul_le_of_le hc hdc
    have hprod := natDegree_mul_le_of_le hc' hd
    omega
  have hcast2 : ((2 * n : ℕ) : k) = (2 : k) * (n : k) :=
    residualHalfRadiusBoundary_cast2 n
  have h0Bd : (A * B ^ 2 * derivative d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow2
  have h0BB : (A * B * derivative B * d).coeff idx = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow3
  have h0ce : (3 : k) * (B * c * derivative e).coeff idx = 0 := by
    rw [coeff_eq_zero_of_natDegree_lt hlow4, mul_zero]
  have h0dd : (3 : k) * (B * d * derivative d).coeff idx = 0 := by
    rw [coeff_eq_zero_of_natDegree_lt hlow5, mul_zero]
  have h0d2 : (3 : k) * (derivative B * d ^ 2).coeff idx = 0 := by
    rw [coeff_eq_zero_of_natDegree_lt hlow6, mul_zero]
  have h0cc : (3 : k) * (c * derivative c * d).coeff idx = 0 := by
    rw [coeff_eq_zero_of_natDegree_lt hlow7, mul_zero]
  have hinner : inner.coeff idx =
      -(2 : k) * (n : k) * A.coeff (2 * n) ^ 2 * Q.coeff (8 * n) -
        (2 / 9 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
          B.coeff (3 * n - g) ^ 3 +
        (2 : k) * (n : k) * A.coeff (2 * n) * B.coeff (3 * n - g) *
          c.coeff (4 * n - g) ^ 2 -
        (6 : k) * (n : k) * A.coeff (2 * n) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
    dsimp [inner, residualHalfRadiusBoundaryRowZeroInner68]
    simp only [coeff_add, coeff_sub, coeff_neg, coeff_smul, smul_eq_mul]
    rw [hAAQ', hAAB', hABc', hAde', h0Bd, h0BB, h0ce, h0dd, h0d2, h0cc, hcast2]
    ring
  rw [residualHalfRadiusBoundaryRowZero_eq_inner68, coeff_smul, smul_eq_mul]
  change ((4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  simp only [Q, hQ8]
  ring

/-! ## Combined coefficients and `l = 0` -/

set_option maxHeartbeats 4000000 in
theorem cubicRowTwoPolynomial68_coeff_residualHalfRadiusBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallg : n = 3 * g) (hwallh : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (10 * n - 1) =
      residualHalfRadiusBoundaryTwoScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsmall : 2 * g < n := residualHalfRadiusBoundary_twoGap n g hg hwallg
  have hhom := secondaryResidualRowTwoPolynomial68_coeff_halfRadiusBoundary
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hn hg hwallg hwallh hA hB hc hd he hi4
  have hload := cubicLoadRowTwoPolynomial68_coeff_halfRadius
    l alpha beta gamma delta epsilon zeta eta A B c D e n g h
    hn hg hsmall hwallh hA hB hc hD he
  rw [coeff_add, hhom]
  change _ +
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e).coeff (10 * n - 1) = _
  rw [hload]
  simp only [residualHalfRadiusBoundaryTwoScalar68]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicRowZeroPolynomial68_coeff_residualHalfRadiusBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallg : n = 3 * g) (hwallh : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) =
      residualHalfRadiusBoundaryZeroScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
        (e.coeff (6 * n - h)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hsmall : 2 * g < n := residualHalfRadiusBoundary_twoGap n g hg hwallg
  have hhom := secondaryResidualRowZeroPolynomial68_coeff_halfRadiusBoundary
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hn hg hwallg hwallh hA hB hc hd he hi4
  have hload := cubicLoadRowZeroPolynomial68_coeff_halfRadius
    l alpha beta gamma delta epsilon zeta eta A B c D e n g h
    hn hg hsmall hwallh hA hB hc hD he
  rw [coeff_add, hhom]
  change _ +
      (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e).coeff (12 * n - 1) = _
  rw [hload]
  simp only [residualHalfRadiusBoundaryZeroScalar68]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicRowTwoZeroPolynomial68_imp_loadL_eq_zero_of_halfRadiusBoundary
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallg : n = 3 * g) (hwallh : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hsumTwo : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hsumZero : (secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e).coeff (12 * n - 1) = 0) :
    l = 0 := by
  have htwo := congrArg (fun p : k[X] => p.coeff (10 * n - 1)) hsumTwo
  rw [cubicRowTwoPolynomial68_coeff_residualHalfRadiusBoundary
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hwallg hwallh hA hB hc hd he hi4, coeff_zero] at htwo
  have hzero := hsumZero
  rw [cubicRowZeroPolynomial68_coeff_residualHalfRadiusBoundary
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hwallg hwallh hA hB hc hd he hi4] at hzero
  exact residualHalfRadiusBoundary_two_zero_force_l (n : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) l
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) ha htwo hzero

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualHalfRadiusBoundary_loadL_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallg : n = 3 * g) (hwallh : 2 * h = n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hrowTwo :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta A B C0 D0)
        (integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D0 E0) B C0 D0 E0 = 0)
    (hrowZero : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (12 * n - 1) = 0) :
    l = 0 := by
  have hsumTwo := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta A B c d e hrowTwo
  let D0 := (1 / 3 : k) • (A * B) + d
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hsum :
      lowerRowZeroPolynomial68
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B
          ((1 / 3 : k) • A ^ 2 + c) D0
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
          ((1 / 3 : k) • A ^ 2 + c) D0
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        D0 ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c D0 e := by
    rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
      show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
          secondaryResidualRowZeroPolynomial68 A B c d e by
        simpa only [D0] using
          cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e]
  have hsumZero :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
          A B c D0 e).coeff (12 * n - 1) = 0 := by
    have hzEq := congrArg (fun p : k[X] => p.coeff (12 * n - 1)) hsum
    simpa only [D0] using hzEq.symm.trans hrowZero
  exact cubicRowTwoZeroPolynomial68_imp_loadL_eq_zero_of_halfRadiusBoundary
    l alpha beta gamma delta epsilon zeta eta i4 A B c d e n g h
    hn hg hwallg hwallh hA ha hB hc hd he hi4 hsumTwo (by
      simpa only [D0] using hsumZero)

/-! ## Canonical expanded wrapper -/

theorem residualHalfRadiusBoundaryRowZeroIndex68_gt_fiftyNine
    (n h : ℕ) (hn : 10 ≤ n) (hwallh : 2 * h = n) :
    59 < 12 * n - 1 :=
  residualHalfRadiusLoadWallRowZeroIndex68_gt_fiftyNine n h hn hwallh

set_option maxHeartbeats 8000000 in
/-- On the canonical expanded system, the mixed residual half-radius wall
`n = 3g` and `2h = n` forces `l = 0`.  The tracked load-zero endgame then
closes the branch.  No residual-support premise is required. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusBoundaryWall_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwallg :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 3 * g)
    (hwallh :
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
      2 * h = n) :
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
  change n = 3 * g at hwallg
  change 2 * h = n at hwallh
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
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hsmall : 2 * g < n := residualHalfRadiusBoundary_twoGap n g hg hwallg
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h2c :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Crec
          Drec Erec)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (12 * n - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (residualHalfRadiusBoundaryRowZeroIndex68_gt_fiftyNine n h hnlarge hwallh)
  have h0c : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be
        ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta Ae Be
        ((1 / 3 : k) • Ae ^ 2 + ce) ((1 / 3 : k) • (Ae * Be) + d)
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee))
      ((1 / 3 : k) • (Ae * Be) + d)
        ((1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee)).coeff
          (12 * n - 1) = 0 := by
    simpa only [← hCrec, ← hDrec, ← hErec] using h0target
  have hl0 := polynomialSecondaryResidualHalfRadiusBoundary_loadL_eq_zero68
    l alpha beta gamma delta epsilon zeta eta i4 Ae Be ce d ee n g h
    hn hg hwallg hwallh hA ha hB hc hbounds.1 hbounds.2 hi4c h2c h0c
  exact maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hl0 (by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)

#print axioms residualHalfRadiusBoundary_two_zero_force_l
#print axioms secondaryResidualRowTwoPolynomial68_coeff_halfRadiusBoundary
#print axioms secondaryResidualRowZeroPolynomial68_coeff_halfRadiusBoundary
#print axioms polynomialSecondaryResidualHalfRadiusBoundary_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusBoundaryWall_impossible68

end Max11DegreeRoutes
