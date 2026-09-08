import LowScale410ScaleZeroGammaZeroBFace

/-!
# Exact nonzero-gamma fan on `U=0`

After `U=A^2-4C0=0`, the second conserved polynomial has only three
possible top faces: `B^4`, `gamma A B^2`, and `delta A^2 B`; the zeta and
theta terms are strictly lower when both coordinate degrees are positive.
This reduces the surviving competition to two exact degree rays, together
with their leading-coefficient cancellation walls.  Coordinate-degree-zero
boundaries are retained honestly.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaUZeroCompetition410

variable {k : Type*} [Field k] [CharZero k]

def gammaUZeroLowerRestOne410
    (zeta theta : k) (A B : k[X]) : k[X] :=
  -(3 / 4 * zeta : k) • (A * B) + theta • B

theorem firstIntegralOne410_discriminantZero_specialization
    (gamma delta zeta eta theta : k) (A B : k[X]) :
    firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) =
      (-(5 / 32 : k)) • B ^ 4 -
        (3 / 4 * gamma : k) • (A * B ^ 2) -
        (5 / 32 * delta : k) • (A ^ 2 * B) +
        gammaUZeroLowerRestOne410 zeta theta A B := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [firstIntegralOnePolynomial410, gammaUZeroLowerRestOne410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_zero,
    map_mul]
  ring

def GammaUZeroPositiveDegreeFan410
    (gamma delta : k) (A B : k[X]) : Prop :=
  (delta = 0 ∧ A.natDegree = 2 * B.natDegree ∧
      5 * B.leadingCoeff ^ 2 + 24 * gamma * A.leadingCoeff = 0) ∨
    (delta ≠ 0 ∧ 2 * A.natDegree = 3 * B.natDegree ∧
      B.leadingCoeff ^ 3 + delta * A.leadingCoeff ^ 2 = 0)

theorem constantIntegralOne410_gamma_U_zero_positive_degree_fan
    (gamma delta zeta eta theta k1 : k) (A B : k[X])
    (hgamma : gamma ≠ 0) (hApos : 0 < A.natDegree)
    (hBpos : 0 < B.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k1) :
    GammaUZeroPositiveDegreeFan410 gamma delta A B := by
  have hA : A ≠ 0 := by
    intro hzero
    subst A
    rw [natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    subst B
    rw [natDegree_zero] at hBpos
    omega
  have hAB2deg : (A * B ^ 2).natDegree =
      A.natDegree + 2 * B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
  have hA2Bdeg : (A ^ 2 * B).natDegree =
      2 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
  have hB4deg : (B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
  have hspecial := hOne
  rw [firstIntegralOne410_discriminantZero_specialization] at hspecial
  by_cases hdelta : delta = 0
  · have heq : (-(5 / 32 : k)) • B ^ 4 +
        ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
          gammaUZeroLowerRestOne410 zeta theta A B) = C k1 := by
      simpa [hdelta, sub_eq_add_neg, add_assoc] using hspecial
    have hdegrees : A.natDegree + 2 * B.natDegree =
        4 * B.natDegree := by
      rcases lt_trichotomy
          (A.natDegree + 2 * B.natDegree) (4 * B.natDegree) with
        hlt | hequal | hgt
      · have hrest :
            ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
              gammaUZeroLowerRestOne410 zeta theta A B).natDegree <
                4 * B.natDegree := by
          simp only [gammaUZeroLowerRestOne410]
          compute_degree
          omega
        exact (smul_add_lower_ne_C410 (-(5 / 32 : k)) k1 (B ^ 4)
          ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
            gammaUZeroLowerRestOne410 zeta theta A B)
          (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB)
          (by omega) hB4deg hrest heq).elim
      · exact hequal
      · have hrest :
            ((-(5 / 32 : k)) • B ^ 4 +
              gammaUZeroLowerRestOne410 zeta theta A B).natDegree <
                A.natDegree + 2 * B.natDegree := by
          simp only [gammaUZeroLowerRestOne410]
          compute_degree
          omega
        have heq' : (-(3 / 4 * gamma : k)) • (A * B ^ 2) +
            ((-(5 / 32 : k)) • B ^ 4 +
              gammaUZeroLowerRestOne410 zeta theta A B) = C k1 := by
          simpa only [add_assoc, add_left_comm, add_comm] using heq
        exact (smul_add_lower_ne_C410 (-(3 / 4 * gamma : k)) k1
          (A * B ^ 2)
          ((-(5 / 32 : k)) • B ^ 4 +
            gammaUZeroLowerRestOne410 zeta theta A B)
          (A.natDegree + 2 * B.natDegree)
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hgamma))
          (mul_ne_zero hA (pow_ne_zero 2 hB)) (by omega) hAB2deg hrest
          heq').elim
    have hrest : (gammaUZeroLowerRestOne410 zeta theta A B).natDegree <
        4 * B.natDegree := by
      simp only [gammaUZeroLowerRestOne410]
      compute_degree
      omega
    have hcoeff := congrArg
      (fun P : k[X] => P.coeff (4 * B.natDegree)) heq
    rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
      show (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 by
        rw [← hB4deg, coeff_natDegree, leadingCoeff_pow],
      show (A * B ^ 2).coeff (4 * B.natDegree) =
          A.leadingCoeff * B.leadingCoeff ^ 2 by
        rw [← hdegrees, ← hAB2deg, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_pow],
      coeff_eq_zero_of_natDegree_lt hrest, add_zero,
      show (C k1 : k[X]).coeff (4 * B.natDegree) = 0 by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_C]
        omega] at hcoeff
    simp only [smul_eq_mul] at hcoeff
    have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
    left
    refine ⟨hdelta, by omega, ?_⟩
    apply (mul_left_cancel₀ (pow_ne_zero 2 hBlc))
    linear_combination (-32 : k) * hcoeff
  · have heq : (-(5 / 32 : k)) • B ^ 4 +
        ((-(5 / 32 * delta : k)) • (A ^ 2 * B) +
          ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
            gammaUZeroLowerRestOne410 zeta theta A B)) = C k1 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hspecial
    have hdegrees : 2 * A.natDegree + B.natDegree =
        4 * B.natDegree := by
      rcases lt_trichotomy
          (2 * A.natDegree + B.natDegree) (4 * B.natDegree) with
        hlt | hequal | hgt
      · have hrest :
            ((-(5 / 32 * delta : k)) • (A ^ 2 * B) +
              ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
                gammaUZeroLowerRestOne410 zeta theta A B)).natDegree <
                  4 * B.natDegree := by
          simp only [gammaUZeroLowerRestOne410]
          compute_degree
          omega
        exact (smul_add_lower_ne_C410 (-(5 / 32 : k)) k1 (B ^ 4)
          ((-(5 / 32 * delta : k)) • (A ^ 2 * B) +
            ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
              gammaUZeroLowerRestOne410 zeta theta A B))
          (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB)
          (by omega) hB4deg hrest heq).elim
      · exact hequal
      · have hrest :
            ((-(5 / 32 : k)) • B ^ 4 +
              ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
                gammaUZeroLowerRestOne410 zeta theta A B)).natDegree <
                  2 * A.natDegree + B.natDegree := by
          simp only [gammaUZeroLowerRestOne410]
          compute_degree
          omega
        have heq' : (-(5 / 32 * delta : k)) • (A ^ 2 * B) +
            ((-(5 / 32 : k)) • B ^ 4 +
              ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
                gammaUZeroLowerRestOne410 zeta theta A B)) = C k1 := by
          simpa only [add_assoc, add_left_comm, add_comm] using heq
        exact (smul_add_lower_ne_C410 (-(5 / 32 * delta : k)) k1
          (A ^ 2 * B)
          ((-(5 / 32 : k)) • B ^ 4 +
            ((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
              gammaUZeroLowerRestOne410 zeta theta A B))
          (2 * A.natDegree + B.natDegree)
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
          (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hA2Bdeg hrest
          heq').elim
    have hgammaLower : A.natDegree + 2 * B.natDegree <
        4 * B.natDegree := by omega
    have hrest :
        (((-(3 / 4 * gamma : k)) • (A * B ^ 2) +
          gammaUZeroLowerRestOne410 zeta theta A B)).natDegree <
            4 * B.natDegree := by
      simp only [gammaUZeroLowerRestOne410]
      compute_degree
      omega
    have hcoeff := congrArg
      (fun P : k[X] => P.coeff (4 * B.natDegree)) heq
    rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
      show (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 by
        rw [← hB4deg, coeff_natDegree, leadingCoeff_pow],
      show (A ^ 2 * B).coeff (4 * B.natDegree) =
          A.leadingCoeff ^ 2 * B.leadingCoeff by
        rw [← hdegrees, ← hA2Bdeg, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_pow],
      coeff_eq_zero_of_natDegree_lt hrest, add_zero,
      show (C k1 : k[X]).coeff (4 * B.natDegree) = 0 by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_C]
        omega] at hcoeff
    simp only [smul_eq_mul] at hcoeff
    have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
    right
    refine ⟨hdelta, by omega, ?_⟩
    apply (mul_left_cancel₀ hBlc)
    linear_combination (-32 / 5 : k) * hcoeff

def GammaUZeroFan410 (gamma delta : k) (A B : k[X]) : Prop :=
  A.natDegree = 0 ∨ B.natDegree = 0 ∨
    GammaUZeroPositiveDegreeFan410 gamma delta A B

theorem constantIntegralOne410_gamma_U_zero_fan
    (gamma delta zeta eta theta k1 : k) (A B : k[X])
    (hgamma : gamma ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k1) :
    GammaUZeroFan410 gamma delta A B := by
  by_cases hA0 : A.natDegree = 0
  · exact Or.inl hA0
  right
  by_cases hB0 : B.natDegree = 0
  · exact Or.inl hB0
  right
  exact constantIntegralOne410_gamma_U_zero_positive_degree_fan
    gamma delta zeta eta theta k1 A B hgamma (by omega) (by omega) hOne

def UZeroFanRefinedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  ZeroBDeletedGammaNewtonResidual410 delta zeta eta theta A B C0 ∧
    (A ^ 2 - (4 : k) • C0 ≠ 0 ∨ GammaUZeroFan410 gamma delta A B)

theorem zeroBDeletedGammaNewtonResidual410_U_zero_fan_refinement
    (gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hgamma : gamma ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hold : ZeroBDeletedGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    UZeroFanRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  by_cases hU : A ^ 2 - (4 : k) • C0 = 0
  · right
    have hAC : A ^ 2 = (4 : k) • C0 := sub_eq_zero.mp hU
    have hC0 : C0 = (1 / 4 : k) • A ^ 2 := by
      calc
        C0 = (1 / 4 : k) • ((4 : k) • C0) := by module
        _ = (1 / 4 : k) • A ^ 2 := by rw [← hAC]
    rw [hC0] at hOne
    exact constantIntegralOne410_gamma_U_zero_fan
      gamma delta zeta eta theta k1 A B hgamma hOne
  · exact Or.inl hU

/-! ## Source-facing refinement -/

def GammaUZeroFanNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      UZeroFanRefinedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaUZeroFanNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota k2 k1
      terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    l = 0 ∧
      GammaUZeroFanNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaZeroBDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      zeroBDeletedGammaNewtonResidual410_U_zero_fan_refinement
        gamma delta zeta eta theta k1 A B C0 hgamma.2.1 hOne0
          hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaUZeroFanNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaUZeroFanNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaUZeroFanNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaUZeroFanNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaUZeroFanNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaUZeroFanNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaUZeroCompetition410

end Max11DegreeRoutes
