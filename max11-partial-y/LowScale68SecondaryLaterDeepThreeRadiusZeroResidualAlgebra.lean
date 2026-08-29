import LowScale68SecondaryLaterDeepThreeRadiusResidualSelector

/-! # Algebra of the zero residual leaf on `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusZeroResidualAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The exact I4 polynomial after `l=beta=d=e=0`. -/
def threeRadiusZeroResidualI4Polynomial68
    (delta epsilon zeta : k) (A B c : k[X]) : k[X] :=
  (-8 / 27 : k) • B ^ 3 + zeta • A + (2 * epsilon : k) • B +
    (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c

set_option maxHeartbeats 4000000 in
theorem cubicFirstIntegralFourPolynomial68_threeRadiusZeroResidual
    (gamma delta epsilon zeta : k) (A B c : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
        A B c ((1 / 3 : k) • (A * B)) 0 =
      threeRadiusZeroResidualI4Polynomial68 delta epsilon zeta A B c := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicFirstIntegralFourPolynomial68,
    threeRadiusZeroResidualI4Polynomial68, smul_zero, mul_zero, add_zero,
    sub_zero, zero_smul, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 5000000 in
/-- I4 has a unique top `B³` term on the three-radius wall. -/
theorem threeRadiusZeroResidualI4_forces_B_top_zero68
    (gamma delta epsilon zeta i4 : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B)) 0 = C i4) :
    B.coeff (3 * n - g) = 0 := by
  rw [cubicFirstIntegralFourPolynomial68_threeRadiusZeroResidual] at hi4
  have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hB
  have hidx : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
  rw [hidx] at hB3
  have hAlt : A.natDegree < 9 * n - 3 * g := hA.trans_lt (by omega)
  have hBlt : B.natDegree < 9 * n - 3 * g := hB.trans_lt (by omega)
  have hA2lt : (A ^ 2).natDegree < 9 * n - 3 * g := by
    compute_degree
    omega
  have hclt : c.natDegree < 9 * n - 3 * g := hc.trans_lt (by omega)
  have hi : 9 * n - 3 * g ≠ 0 := by omega
  have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
  simp only [threeRadiusZeroResidualI4Polynomial68, coeff_add, coeff_smul,
    smul_eq_mul, hB3, coeff_eq_zero_of_natDegree_lt hAlt,
    coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hA2lt,
    coeff_eq_zero_of_natDegree_lt hclt, mul_zero, add_zero,
    coeff_C, if_neg hi] at hz
  have hb3 : B.coeff (3 * n - g) ^ 3 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact eq_zero_of_pow_eq_zero hb3

set_option maxHeartbeats 5000000 in
/-- The zero residual homogeneous row has a unique top `c²c'` term after
the `B` edge drops. -/
theorem secondaryResidualRowOnePolynomial68_coeff_threeRadiusZeroResidual
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwall : 2 * g = 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree < 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (secondaryResidualRowOnePolynomial68 A B c 0 0).coeff
        (12 * n - 3 * g - 1) =
      (-8 / 9 : k) * ((4 * n - g : ℕ) : k) *
        c.coeff (4 * n - g) ^ 3 := by
  have hAB2c : (derivative A * B ^ 2 * c).natDegree <
      12 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hcc := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hi : 2 * (4 * n - g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi, hc2] at hcc
  simp only [secondaryResidualRowOnePolynomial68, zero_mul, mul_zero,
    derivative_zero, zero_pow, smul_zero, add_zero, sub_zero, coeff_smul,
    coeff_add, coeff_sub, coeff_eq_zero_of_natDegree_lt hAB2c, hcc,
    smul_eq_mul, mul_zero, zero_add]
  simp only [coeff_zero, zero_pow, mul_zero]
  have hz2 : (0 : k[X]) ^ 2 = 0 := by norm_num
  rw [hz2, mul_zero, coeff_zero]
  ring

#print axioms cubicFirstIntegralFourPolynomial68_threeRadiusZeroResidual
#print axioms threeRadiusZeroResidualI4_forces_B_top_zero68
#print axioms secondaryResidualRowOnePolynomial68_coeff_threeRadiusZeroResidual

end LaterDeepThreeRadiusZeroResidualAlgebra68

end Max11DegreeRoutes
