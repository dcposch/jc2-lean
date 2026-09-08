import LowScale68SecondaryLaterDeepFiveRadiusExactWalls

/-! # The zero residual pair on `2g = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusZeroResidual68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def fiveRadiusZeroResidualI4Polynomial68
    (epsilon zeta : k) (A B : k[X]) : k[X] :=
  (-8 / 27 : k) • B ^ 3 + zeta • A + (2 * epsilon : k) • B

set_option maxHeartbeats 4000000 in
theorem cubicFirstIntegralFourPolynomial68_zeroResidual
    (gamma epsilon zeta : k) (A B c : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B)) 0 =
      fiveRadiusZeroResidualI4Polynomial68 epsilon zeta A B := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicFirstIntegralFourPolynomial68,
    fiveRadiusZeroResidualI4Polynomial68, smul_zero, mul_zero, add_zero,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem fiveRadiusZeroResidualI4_forces_zeta_zero68
    (gamma epsilon zeta i4 : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4) :
    zeta = 0 := by
  rw [cubicFirstIntegralFourPolynomial68_zeroResidual] at hi4
  have hB3 : (B ^ 3).natDegree < 2 * n := by
    compute_degree
    omega
  have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
  have hz := congrArg (fun p : k[X] => p.coeff (2 * n)) hi4
  have hi : 2 * n ≠ 0 := by omega
  simp only [fiveRadiusZeroResidualI4Polynomial68, coeff_add, coeff_smul,
    smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3,
    coeff_eq_zero_of_natDegree_lt hBlt, mul_zero, zero_add,
    coeff_C, if_neg hi] at hz
  exact (mul_eq_zero.mp (by simpa only [add_zero] using hz)).resolve_right ha

set_option maxHeartbeats 5000000 in
theorem fiveRadiusZeroResidualI4_forces_B_top_zero68
    (gamma epsilon i4 : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4) :
    B.coeff (3 * n - g) = 0 := by
  rw [cubicFirstIntegralFourPolynomial68_zeroResidual] at hi4
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hidx : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hidx] at hB3
  have hBlt : B.natDegree < 9 * n - 3 * g := hB.trans_lt (by omega)
  have hi : 9 * n - 3 * g ≠ 0 := by omega
  have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
  simp only [fiveRadiusZeroResidualI4Polynomial68, zero_smul, add_zero,
    coeff_add, coeff_smul, smul_eq_mul, hB3,
    coeff_eq_zero_of_natDegree_lt hBlt, mul_zero, add_zero,
    coeff_C, if_neg hi] at hz
  have hb3 : B.coeff (3 * n - g) ^ 3 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact eq_zero_of_pow_eq_zero hb3

def fiveRadiusZeroResidualRowOneCore68 (c : k[X]) : k[X] :=
  (-8 / 9 : k) • (c ^ 2 * derivative c)

def fiveRadiusZeroResidualRowOneTail68
    (gamma : k) (A B c : k[X]) : k[X] :=
  (8 / 27 : k) • derivative (A * B ^ 2 * c) +
    gamma •
      ((-4 / 3 : k) • (c * derivative c) +
        (2 / 9 : k) • (derivative A * B ^ 2) +
        (4 / 9 : k) • (A * B * derivative B))

theorem fiveRadiusReducedRowOnePolynomial68_zeroResidualSplit
    (gamma epsilon : k) (A B c : k[X]) :
    fiveRadiusReducedRowOnePolynomial68 gamma epsilon 0 A B c 0 0 =
      fiveRadiusZeroResidualRowOneCore68 c +
        fiveRadiusZeroResidualRowOneTail68 gamma A B c := by
  simp only [fiveRadiusReducedRowOnePolynomial68,
    fiveRadiusZeroResidualRowOneCore68, fiveRadiusZeroResidualRowOneTail68,
    mul_zero, zero_mul, pow_two, derivative_zero, smul_zero, zero_smul,
    add_zero, zero_add, sub_zero]
  module

set_option maxHeartbeats 5000000 in
theorem fiveRadiusZeroResidualRowOneTail68_degree_lt
    (gamma : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree < 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusZeroResidualRowOneTail68 gamma A B c).natDegree <
      12 * n - 3 * g - 1 := by
  let idx := 12 * n - 3 * g - 1
  have hAB2cprod : (A * B ^ 2 * c).natDegree < 12 * n - 3 * g := by
    compute_degree
    omega
  have hAB2c : (derivative (A * B ^ 2 * c)).natDegree < idx := by
    have hle := natDegree_derivative_le (A * B ^ 2 * c)
    dsimp [idx]
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
  simp only [fiveRadiusZeroResidualRowOneTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_smul_lt68 (8 / 27 : k) hAB2c)
    (deepGap_natDegree_smul_lt68 gamma
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_smul_lt68 (-4 / 3 : k) hcc)
          (deepGap_natDegree_smul_lt68 (2 / 9 : k) hApB2))
        (deepGap_natDegree_smul_lt68 (4 / 9 : k) hABBp)))

set_option maxHeartbeats 5000000 in
theorem fiveRadiusZeroResidualRowOneCore68_coeff
    (c : k[X]) (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusZeroResidualRowOneCore68 c).coeff (12 * n - 3 * g - 1) =
      (-8 / 9 : k) * ((4 * n - g : ℕ) : k) *
        c.coeff (4 * n - g) ^ 3 := by
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hi : 2 * (4 * n - g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi, hc2] at hc3
  simp only [fiveRadiusZeroResidualRowOneCore68, coeff_smul,
    smul_eq_mul, hc3]
  ring

set_option maxHeartbeats 8000000 in
theorem fiveRadius_zeroResidual_impossible68
    (gamma epsilon zeta i4 : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨
      c.coeff (4 * n - g) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4)
    (hrow : fiveRadiusReducedRowOnePolynomial68
      gamma epsilon zeta A B c 0 0 = 0) : False := by
  have hzeta := fiveRadiusZeroResidualI4_forces_zeta_zero68
    gamma epsilon zeta i4 A B c n g hn hwall ha hA hB hi4
  have hi40 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4 := by
    simpa only [hzeta] using hi4
  have hb := fiveRadiusZeroResidualI4_forces_B_top_zero68
    gamma epsilon i4 A B c n g hn hwall hB hi40
  have hindex : 0 < 3 * n - g := by omega
  have hBlt := natDegree_lt_of_le_of_coeff_eq_zero68
    B (3 * n - g) hindex hB hb
  have hcne : c.coeff (4 * n - g) ≠ 0 := by
    exact hsupport.resolve_left (not_ne_iff.mpr hb)
  have htail := fiveRadiusZeroResidualRowOneTail68_degree_lt
    gamma A B c n g hn hwall hA hBlt hc
  have hcore := fiveRadiusZeroResidualRowOneCore68_coeff
    c n g hn hwall hc
  have hrow0 : fiveRadiusReducedRowOnePolynomial68
      gamma epsilon 0 A B c 0 0 = 0 := by
    simpa only [hzeta] using hrow
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrow0
  rw [fiveRadiusReducedRowOnePolynomial68_zeroResidualSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore, coeff_zero] at hcoeff
  have hcast : (((4 * n - g : ℕ) : k)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hcast)
    (pow_ne_zero 3 hcne)) hcoeff

#print axioms fiveRadius_zeroResidual_impossible68

end LaterDeepFiveRadiusZeroResidual68

end Max11DegreeRoutes
