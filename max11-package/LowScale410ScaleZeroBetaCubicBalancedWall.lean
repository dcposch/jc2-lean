import LowScale410ScaleZeroBetaCubicHighCTie

/-!
# The balanced beta-cubic wall

This closes the last degree chamber on the beta cubic wall.  At
`deg C0 = 2 deg A`, the cubic Newton equation forces `2 deg B ≤ 3 deg A`.
The strict inequality is incompatible with the top coefficient of the
second invariant.  At equality, the cubic wall and the two zero-load
invariants give three homogeneous leading-coefficient equations whose
resultant is nonzero.  The degree-zero endpoint is excluded by the
nonzero terminal row.  No later load is assumed to vanish.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section BetaCubicBalancedWall410

variable {k : Type*} [Field k] [CharZero k]

/-! ## Exact leading faces -/

/-- The `A,C0` part of the zero-load second invariant.  It is the complete
top face in the strict chamber `2 deg B < 3 deg A`. -/
def betaCubicBalancedStrictOneFace410 (A C0 : k[X]) : k[X] :=
  -(5 / 256 : k) • A ^ 6 + (15 / 64 : k) • (A ^ 4 * C0) -
    (15 / 16 : k) • (A ^ 2 * C0 ^ 2) + (5 / 4 : k) • C0 ^ 3

/-- All terms below the strict balanced `I1` face. -/
def betaCubicBalancedStrictOneRest410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (15 / 32 : k) • (A ^ 3 * B ^ 2) -
    (15 / 8 : k) • (A * B ^ 2 * C0) - (5 / 32 : k) • B ^ 4 +
      betaLoadOneRest410 gamma delta zeta eta theta A B C0

theorem firstIntegralOne410_eq_balancedStrictFace_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    firstIntegralOnePolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      betaCubicBalancedStrictOneFace410 A C0 +
        betaCubicBalancedStrictOneRest410 gamma delta zeta eta theta
          A B C0 := by
  rw [firstIntegralOne410_eq_zero_add_later_of_betaCubicWall
    beta gamma delta zeta eta theta A B C0 hwall,
    zeroLoadOne410_eq]
  simp only [betaCubicBalancedStrictOneFace410,
    betaCubicBalancedStrictOneRest410]
  abel

theorem betaCubicBalancedStrictOneRest410_natDegree_lt
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hstrict : 2 * B.natDegree < 3 * A.natDegree) :
    (betaCubicBalancedStrictOneRest410 gamma delta zeta eta theta
      A B C0).natDegree < 6 * A.natDegree := by
  simp only [betaCubicBalancedStrictOneRest410, betaLoadOneRest410]
  compute_degree
  omega

/-- The complete zero-load `I2` face on the balanced three-face tie. -/
def betaCubicBalancedTieTwoFace410 (A B C0 : k[X]) : k[X] :=
  (-35 / 64 : k) • (A ^ 4 * B) +
    (15 / 8 : k) • (A ^ 2 * B * C0) +
      (15 / 4 : k) • (B * C0 ^ 2)

/-- The beta and later-load `I2` terms, all below the balanced tie face. -/
def betaCubicBalancedTieTwoRest410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  betaLoadTwoPolynomial410 beta A B C0 +
    betaLoadTwoRest410 gamma delta zeta eta theta A B C0

theorem firstIntegralTwo410_eq_balancedTieFace_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    firstIntegralTwoPolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      betaCubicBalancedTieTwoFace410 A B C0 +
        betaCubicBalancedTieTwoRest410 beta gamma delta zeta eta theta
          A B C0 := by
  rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionTwoPolynomial410_eq_beta_add_rest,
    zeroLoadTwo410_eq_betaCubic_decomposition A B C0 hwall]
  simp only [betaCubicBalancedTieTwoFace410,
    betaCubicBalancedTieTwoRest410]

theorem betaCubicBalancedTieTwoRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (htie : 2 * B.natDegree = 3 * A.natDegree) :
    (betaCubicBalancedTieTwoRest410 beta gamma delta zeta eta theta
      A B C0).natDegree < 4 * A.natDegree + B.natDegree := by
  simp only [betaCubicBalancedTieTwoRest410, betaLoadTwoPolynomial410,
    betaLoadTwoRest410]
  compute_degree
  omega

/-- On the balanced tie, every later-load term is below the zero-load
`I1` face at degree `6 deg A`. -/
theorem betaLoadOneRest410_natDegree_lt_balancedTie
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (htie : 2 * B.natDegree = 3 * A.natDegree) :
    (betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree <
      6 * A.natDegree := by
  simp only [betaLoadOneRest410]
  compute_degree
  omega

/-! ## Cubic leading equations -/

theorem betaCubicWall_balanced_strict_leadingCoeff
    (A B C0 : k[X]) (hA : A ≠ 0) (hC0 : C0 ≠ 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hstrict : 2 * B.natDegree < 3 * A.natDegree)
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    (5 : k) * A.leadingCoeff ^ 3 -
        24 * (A.leadingCoeff * C0.leadingCoeff) = 0 := by
  have hA3deg : (A ^ 3).natDegree = 3 * A.natDegree := by
    rw [natDegree_pow]
  have hACdeg : (A * C0).natDegree = 3 * A.natDegree := by
    rw [natDegree_mul hA hC0, hbalanced]
    omega
  have hB2deg : (B ^ 2).natDegree < 3 * A.natDegree := by
    rw [natDegree_pow]
    exact hstrict
  have hA3coeff : (A ^ 3).coeff (3 * A.natDegree) =
      A.leadingCoeff ^ 3 := by
    rw [← hA3deg, coeff_natDegree, leadingCoeff_pow]
  have hACcoeff : (A * C0).coeff (3 * A.natDegree) =
      A.leadingCoeff * C0.leadingCoeff := by
    rw [← hACdeg, coeff_natDegree, leadingCoeff_mul]
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (3 * A.natDegree)) hwall
  simp only [betaOneCorePolynomial410, coeff_sub, coeff_smul,
    hA3coeff, hACcoeff, coeff_eq_zero_of_natDegree_lt hB2deg,
    smul_eq_mul, mul_zero, sub_zero, coeff_zero] at hcoeff
  exact hcoeff

theorem betaCubicWall_balanced_tie_leadingCoeff
    (A B C0 : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hC0 : C0 ≠ 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (htie : 2 * B.natDegree = 3 * A.natDegree)
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    (5 : k) * A.leadingCoeff ^ 3 -
        24 * (A.leadingCoeff * C0.leadingCoeff) -
          4 * B.leadingCoeff ^ 2 = 0 := by
  have hA3deg : (A ^ 3).natDegree = 3 * A.natDegree := by
    rw [natDegree_pow]
  have hACdeg : (A * C0).natDegree = 3 * A.natDegree := by
    rw [natDegree_mul hA hC0, hbalanced]
    omega
  have hB2deg : (B ^ 2).natDegree = 3 * A.natDegree := by
    rw [natDegree_pow, htie]
  have hA3coeff : (A ^ 3).coeff (3 * A.natDegree) =
      A.leadingCoeff ^ 3 := by
    rw [← hA3deg, coeff_natDegree, leadingCoeff_pow]
  have hACcoeff : (A * C0).coeff (3 * A.natDegree) =
      A.leadingCoeff * C0.leadingCoeff := by
    rw [← hACdeg, coeff_natDegree, leadingCoeff_mul]
  have hB2coeff : (B ^ 2).coeff (3 * A.natDegree) =
      B.leadingCoeff ^ 2 := by
    rw [← hB2deg, coeff_natDegree, leadingCoeff_pow]
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (3 * A.natDegree)) hwall
  simp only [betaOneCorePolynomial410, coeff_sub, coeff_smul,
    hA3coeff, hACcoeff, hB2coeff, smul_eq_mul, coeff_zero] at hcoeff
  exact hcoeff

/-! ## Strict balanced chamber -/

theorem betaCubicWall_balanced_strict_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hA : A ≠ 0) (hC0 : C0 ≠ 0)
    (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hstrict : 2 * B.natDegree < 3 * A.natDegree)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hshape := betaCubicWall_balanced_strict_leadingCoeff
    A B C0 hA hC0 hbalanced hstrict hwall
  have hA6deg : (A ^ 6).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow]
  have hA4Cdeg : (A ^ 4 * C0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hC0, natDegree_pow, hbalanced]
    omega
  have hA2C2deg : (A ^ 2 * C0 ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hC0),
      natDegree_pow, natDegree_pow, hbalanced]
    omega
  have hC3deg : (C0 ^ 3).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow, hbalanced]
    omega
  have hA6coeff : (A ^ 6).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 6 := by
    rw [← hA6deg, coeff_natDegree, leadingCoeff_pow]
  have hA4Ccoeff : (A ^ 4 * C0).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 4 * C0.leadingCoeff := by
    rw [← hA4Cdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hA2C2coeff : (A ^ 2 * C0 ^ 2).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
    rw [← hA2C2deg, coeff_natDegree, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow]
  have hC3coeff : (C0 ^ 3).coeff (6 * A.natDegree) =
      C0.leadingCoeff ^ 3 := by
    rw [← hC3deg, coeff_natDegree, leadingCoeff_pow]
  have hrest := betaCubicBalancedStrictOneRest410_natDegree_lt
    gamma delta zeta eta theta A B C0 hApos hbalanced hstrict
  have hk1 : (C k1 : k[X]).coeff (6 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [firstIntegralOne410_eq_balancedStrictFace_add_rest
    beta gamma delta zeta eta theta A B C0 hwall] at hOne
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (6 * A.natDegree)) hOne
  simp only [betaCubicBalancedStrictOneFace410, coeff_add, coeff_sub,
    coeff_smul, coeff_eq_zero_of_natDegree_lt hrest, add_zero,
    hA6coeff, hA4Ccoeff, hA2C2coeff, hC3coeff, smul_eq_mul, hk1]
    at hcoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hshape' :
      (5 : k) * A.leadingCoeff ^ 2 - 24 * C0.leadingCoeff = 0 := by
    apply mul_left_cancel₀ hAle
    linear_combination hshape
  have hpow5 : (5 : k) * A.leadingCoeff ^ 6 = 0 := by
    linear_combination
      -(216 : k) * (256 * hcoeff) +
        (-(2880 : k) * C0.leadingCoeff ^ 2 +
          1560 * A.leadingCoeff ^ 2 * C0.leadingCoeff -
          215 * A.leadingCoeff ^ 4) * hshape'
  have hpow : A.leadingCoeff ^ 6 = 0 :=
    (mul_eq_zero.mp hpow5).resolve_left (by norm_num)
  exact hAle (eq_zero_of_pow_eq_zero hpow)

/-! ## Three-face balanced tie -/

theorem betaCubicWall_balanced_tie_impossible
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hC0 : C0 ≠ 0)
    (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (htie : 2 * B.natDegree = 3 * A.natDegree)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hwallCoeff := betaCubicWall_balanced_tie_leadingCoeff
    A B C0 hA hB hC0 hbalanced htie hwall
  have hA4Bdeg : (A ^ 4 * B).natDegree =
      4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hB, natDegree_pow]
  have hA2BCdeg : (A ^ 2 * B * C0).natDegree =
      4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hA) hB) hC0,
      natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow, hbalanced]
    omega
  have hBC2deg : (B * C0 ^ 2).natDegree =
      4 * A.natDegree + B.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hC0), natDegree_pow, hbalanced]
    omega
  have hA4Bcoeff : (A ^ 4 * B).coeff
      (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff ^ 4 * B.leadingCoeff := by
    rw [← hA4Bdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hA2BCcoeff : (A ^ 2 * B * C0).coeff
      (4 * A.natDegree + B.natDegree) =
        A.leadingCoeff ^ 2 * B.leadingCoeff * C0.leadingCoeff := by
    rw [← hA2BCdeg, coeff_natDegree, leadingCoeff_mul,
      leadingCoeff_mul, leadingCoeff_pow]
  have hBC2coeff : (B * C0 ^ 2).coeff
      (4 * A.natDegree + B.natDegree) =
        B.leadingCoeff * C0.leadingCoeff ^ 2 := by
    rw [← hBC2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hTwoRest := betaCubicBalancedTieTwoRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hApos hbalanced htie
  have hk2 : (C k2 : k[X]).coeff
      (4 * A.natDegree + B.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [firstIntegralTwo410_eq_balancedTieFace_add_rest
    beta gamma delta zeta eta theta A B C0 hwall] at hTwo
  have hTwoCoeff := congrArg
    (fun P : k[X] => P.coeff (4 * A.natDegree + B.natDegree)) hTwo
  simp only [betaCubicBalancedTieTwoFace410, coeff_add, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hTwoRest, add_zero, hA4Bcoeff,
    hA2BCcoeff, hBC2coeff, smul_eq_mul, hk2] at hTwoCoeff
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hTwoScalar :
      -(35 : k) * A.leadingCoeff ^ 4 +
          120 * (A.leadingCoeff ^ 2 * C0.leadingCoeff) +
            240 * C0.leadingCoeff ^ 2 = 0 := by
    apply mul_left_cancel₀ hBle
    linear_combination 64 * hTwoCoeff
  have hA6deg : (A ^ 6).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow]
  have hA4Cdeg : (A ^ 4 * C0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hC0, natDegree_pow, hbalanced]
    omega
  have hA3B2deg : (A ^ 3 * B ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) (pow_ne_zero 2 hB),
      natDegree_pow, natDegree_pow, htie]
    omega
  have hA2C2deg : (A ^ 2 * C0 ^ 2).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) (pow_ne_zero 2 hC0),
      natDegree_pow, natDegree_pow, hbalanced]
    omega
  have hAB2Cdeg : (A * B ^ 2 * C0).natDegree = 6 * A.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hC0,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow, htie, hbalanced]
    omega
  have hB4deg : (B ^ 4).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow]
    omega
  have hC3deg : (C0 ^ 3).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow, hbalanced]
    omega
  have hA6coeff : (A ^ 6).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 6 := by
    rw [← hA6deg, coeff_natDegree, leadingCoeff_pow]
  have hA4Ccoeff : (A ^ 4 * C0).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 4 * C0.leadingCoeff := by
    rw [← hA4Cdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hA3B2coeff : (A ^ 3 * B ^ 2).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 := by
    rw [← hA3B2deg, coeff_natDegree, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow]
  have hA2C2coeff : (A ^ 2 * C0 ^ 2).coeff (6 * A.natDegree) =
      A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2 := by
    rw [← hA2C2deg, coeff_natDegree, leadingCoeff_mul,
      leadingCoeff_pow, leadingCoeff_pow]
  have hAB2Ccoeff : (A * B ^ 2 * C0).coeff (6 * A.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C0.leadingCoeff := by
    rw [← hAB2Cdeg, coeff_natDegree, leadingCoeff_mul,
      leadingCoeff_mul, leadingCoeff_pow]
  have hB4coeff : (B ^ 4).coeff (6 * A.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hB4deg, coeff_natDegree, leadingCoeff_pow]
  have hC3coeff : (C0 ^ 3).coeff (6 * A.natDegree) =
      C0.leadingCoeff ^ 3 := by
    rw [← hC3deg, coeff_natDegree, leadingCoeff_pow]
  have hOneRest := betaLoadOneRest410_natDegree_lt_balancedTie
    gamma delta zeta eta theta A B C0 hApos hbalanced htie
  have hk1 : (C k1 : k[X]).coeff (6 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [firstIntegralOne410_eq_zero_add_later_of_betaCubicWall
    beta gamma delta zeta eta theta A B C0 hwall,
    zeroLoadOne410_eq] at hOne
  have hOneCoeff := congrArg
    (fun P : k[X] => P.coeff (6 * A.natDegree)) hOne
  simp only [coeff_add, coeff_sub, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hOneRest, add_zero, hA6coeff,
    hA4Ccoeff, hA3B2coeff, hA2C2coeff, hAB2Ccoeff, hB4coeff,
    hC3coeff, smul_eq_mul, hk1] at hOneCoeff
  have hOneReduced :
      (165 : k) * A.leadingCoeff ^ 6 -
          1320 * (A.leadingCoeff ^ 4 * C0.leadingCoeff) +
          2400 * (A.leadingCoeff ^ 2 * C0.leadingCoeff ^ 2) +
          640 * C0.leadingCoeff ^ 3 = 0 := by
    linear_combination
      512 * hOneCoeff +
        ((35 : k) * A.leadingCoeff ^ 3 -
          120 * A.leadingCoeff * C0.leadingCoeff -
          20 * B.leadingCoeff ^ 2) * hwallCoeff
  have hlinear :
      A.leadingCoeff ^ 4 *
        (281 * A.leadingCoeff ^ 2 - 1360 * C0.leadingCoeff) = 0 := by
    linear_combination
      (3 / 5 : k) *
        (hOneReduced -
          ((8 / 3 : k) * C0.leadingCoeff +
            (26 / 3 : k) * A.leadingCoeff ^ 2) * hTwoScalar)
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hlinear' :
      (281 : k) * A.leadingCoeff ^ 2 - 1360 * C0.leadingCoeff = 0 := by
    exact (mul_eq_zero.mp hlinear).resolve_left (pow_ne_zero 4 hAle)
  have hpow923 : (923 : k) * A.leadingCoeff ^ 4 = 0 := by
    linear_combination
      (23120 : k) * hTwoScalar -
        (-(4080 : k) * C0.leadingCoeff -
          2883 * A.leadingCoeff ^ 2) * hlinear'
  have hpow : A.leadingCoeff ^ 4 = 0 :=
    (mul_eq_zero.mp hpow923).resolve_left (by norm_num)
  exact hAle (eq_zero_of_pow_eq_zero hpow)

/-! ## Exhaustive balanced-wall closure -/

theorem betaCubicWall_balanced_degree_le
    (A B C0 : k[X]) (hB : B ≠ 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hwall : betaOneCorePolynomial410 A B C0 = 0) :
    2 * B.natDegree ≤ 3 * A.natDegree := by
  rcases betaCubicWall_degree_split A B C0 hB hwall with hzero | htie
  · rw [hzero.1, natDegree_zero] at hbalanced
    omega
  · rcases htie.2 with h12 | h13 | h23 <;> omega

theorem betaCubicWall_balanced_constants_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X])
    (hA0 : A.natDegree = 0) (hB0 : B.natDegree = 0)
    (hC0 : C0.natDegree = 0) (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hdA : derivative A = 0 := derivative_eq_zero.mpr hA0
  have hdB : derivative B = 0 := derivative_eq_zero.mpr hB0
  have hdC : derivative C0 = 0 := derivative_eq_zero.mpr hC0
  have hdW : derivative
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0) = 0 := by
    simp only [integratedWPolynomial410, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_neg,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_smul, Polynomial.derivative_C,
      Polynomial.derivative_zero, hdA, hdB, hdC, zero_mul, mul_zero,
      add_zero, zero_add, sub_zero, smul_zero]
  have hdZ : derivative
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) = 0 := by
    simp only [integratedZPolynomial410, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_neg,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_smul, Polynomial.derivative_C,
      Polynomial.derivative_zero, hdA, hdB, hdC, zero_mul, mul_zero,
      add_zero, zero_add, sub_zero, smul_zero]
  have hzero : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = 0 := by
    simp [lowerRowZeroPolynomial410, hdW, hdZ, hdC]
  rw [hzero] at hLower
  exact hterminal (C_eq_zero.mp hLower.symm)

/-- Complete exclusion of the last balanced beta-cubic chamber. -/
theorem betaCubicWall_balanced_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hB : B ≠ 0) (hterminal : terminal ≠ 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hA : A ≠ 0 := by
    intro hzero
    have hB2 : B ^ 2 = 0 := by
      simpa [betaOneCorePolynomial410, hzero] using hwall
    exact hB (eq_zero_of_pow_eq_zero hB2)
  have hC0 : C0 ≠ 0 := by
    intro hzero
    subst C0
    exact betaCubicWall_C0_zero_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
        A B hB hterminal hwall hTwo hLower
  have hle := betaCubicWall_balanced_degree_le A B C0 hB hbalanced hwall
  by_cases hApos : 0 < A.natDegree
  · rcases lt_or_eq_of_le hle with hstrict | htie
    · exact betaCubicWall_balanced_strict_impossible
        beta gamma delta zeta eta theta k1 A B C0 hA hC0 hApos
          hbalanced hstrict hwall hOne
    · exact betaCubicWall_balanced_tie_impossible
        beta gamma delta zeta eta theta k2 k1 A B C0 hA hB hC0 hApos
          hbalanced htie hwall hTwo hOne
  · have hA0 : A.natDegree = 0 := by omega
    have hCdeg : C0.natDegree = 0 := by omega
    have hBdeg : B.natDegree = 0 := by omega
    exact betaCubicWall_balanced_constants_impossible
      alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hA0 hBdeg hCdeg hterminal hLower

/-- Source-facing closure: no constant-integral beta-cubic trajectory
survives. -/
theorem constantIntegral410_betaCubicWall_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hB : B ≠ 0) (hterminal : terminal ≠ 0)
    (hwall : betaOneCorePolynomial410 A B C0 = 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  exact betaCubicWall_balanced_impossible
    alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hB hterminal
      (constantIntegral410_betaCubicWall_balanced
        alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
          A B C0 hB hterminal hwall hTwo hLower)
      hwall hTwo hOne hLower

end BetaCubicBalancedWall410

end Max11DegreeRoutes
