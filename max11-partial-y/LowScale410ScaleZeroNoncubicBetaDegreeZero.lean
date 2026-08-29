import LowScale410ScaleZeroCubicDeletedEarlyLoad

/-!
# Removing the degree-zero noncubic beta component

In the genuine noncubic beta packet, the remaining `I1` face was either a
degree competition or the literal component

`deg B = deg (betaOneCorePolynomial410 A B C0) = 0`.

The latter is empty.  If `A` is constant, a nonconstant `C0` exposes the
unique `C0^3` face of `I1`.  If `A` is nonconstant, constancy of the cubic
core forces `deg C0 = 2 deg A`; its leading equation is incompatible with
the top `I1` face.  The all-constant endpoint is killed by the terminal row.
All later loads remain arbitrary.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section NoncubicBetaDegreeZero410

variable {k : Type*} [Field k] [CharZero k]

/-! ## Constant-`A` chamber -/

/-- Everything except the `C0^3` zero-load face of `I1`. -/
def noncubicBetaConstantAOneRest410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  -(5 / 256 : k) • A ^ 6 + (15 / 64 : k) • (A ^ 4 * C0) +
    (15 / 32 : k) • (A ^ 3 * B ^ 2) -
    (15 / 16 : k) • (A ^ 2 * C0 ^ 2) -
    (15 / 8 : k) • (A * B ^ 2 * C0) - (5 / 32 : k) • B ^ 4 +
      betaLoadOnePolynomial410 beta A B C0 +
        betaLoadOneRest410 gamma delta zeta eta theta A B C0

theorem firstIntegralOne410_eq_Ccube_add_constantA_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    firstIntegralOnePolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      (5 / 4 : k) • C0 ^ 3 +
        noncubicBetaConstantAOneRest410
          beta gamma delta zeta eta theta A B C0 := by
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionOnePolynomial410_eq_beta_add_rest, zeroLoadOne410_eq]
  simp only [noncubicBetaConstantAOneRest410]
  abel

theorem noncubicBetaConstantAOneRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hA0 : A.natDegree = 0) (hB0 : B.natDegree = 0)
    (hCpos : 0 < C0.natDegree) :
    (noncubicBetaConstantAOneRest410
      beta gamma delta zeta eta theta A B C0).natDegree <
        3 * C0.natDegree := by
  simp only [noncubicBetaConstantAOneRest410, betaLoadOnePolynomial410,
    betaLoadOneRest410]
  compute_degree
  omega

theorem noncubicBeta_degreeZero_constantA_C_positive_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hA0 : A.natDegree = 0) (hB0 : B.natDegree = 0)
    (hCpos : 0 < C0.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hC0 : C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hCpos
    omega
  have hrest := noncubicBetaConstantAOneRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hA0 hB0 hCpos
  have hfaceDeg : (C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_pow]
  have heq :
      (5 / 4 : k) • C0 ^ 3 +
          noncubicBetaConstantAOneRest410
            beta gamma delta zeta eta theta A B C0 = C k1 := by
    rw [← firstIntegralOne410_eq_Ccube_add_constantA_rest]
    exact hOne
  exact (smul_add_lower_ne_C410 (5 / 4 : k) k1 (C0 ^ 3)
    (noncubicBetaConstantAOneRest410
      beta gamma delta zeta eta theta A B C0)
    (3 * C0.natDegree) (by norm_num) (pow_ne_zero 3 hC0)
    (by omega) hfaceDeg hrest) heq

/-! ## Positive-`A` chamber -/

/-- Constancy of the nonzero cubic core, with constant nonzero `B`, forces
the balanced degree `deg C0 = 2 deg A`. -/
theorem noncubicBeta_constantCore_balanced
    (A B C0 : k[X]) (hApos : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hcore0 : (betaOneCorePolynomial410 A B C0).natDegree = 0) :
    C0.natDegree = 2 * A.natDegree := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  obtain ⟨core, hcoreC⟩ := natDegree_eq_zero.mp hcore0
  rcases lt_trichotomy C0.natDegree (2 * A.natDegree) with hlow | heq | hhigh
  · have hrest :
        ((-(24 : k)) • (A * C0) - (4 : k) • B ^ 2).natDegree <
          3 * A.natDegree := by
      compute_degree
      omega
    have hfaceDeg : (A ^ 3).natDegree = 3 * A.natDegree := by
      rw [natDegree_pow]
    have heqCore :
        (5 : k) • A ^ 3 +
            ((-(24 : k)) • (A * C0) - (4 : k) • B ^ 2) = C core := by
      simpa [betaOneCorePolynomial410, sub_eq_add_neg, neg_smul, add_assoc]
        using hcoreC.symm
    exact (smul_add_lower_ne_C410 (5 : k) core (A ^ 3)
      ((-(24 : k)) • (A * C0) - (4 : k) • B ^ 2)
      (3 * A.natDegree) (by norm_num) (pow_ne_zero 3 hA)
      (by omega) hfaceDeg hrest heqCore).elim
  · exact heq
  · have hC0 : C0 ≠ 0 := by
      intro hzero
      rw [hzero, natDegree_zero] at hhigh
      omega
    have hrest :
        ((5 : k) • A ^ 3 - (4 : k) • B ^ 2).natDegree <
          A.natDegree + C0.natDegree := by
      compute_degree
      omega
    have hfaceDeg : (A * C0).natDegree =
        A.natDegree + C0.natDegree := by
      rw [natDegree_mul hA hC0]
    have heqCore :
        (-(24 : k)) • (A * C0) +
            ((5 : k) • A ^ 3 - (4 : k) • B ^ 2) = C core := by
      simpa [betaOneCorePolynomial410, sub_eq_add_neg, neg_smul,
        add_comm, add_left_comm, add_assoc] using hcoreC.symm
    exact (smul_add_lower_ne_C410 (-(24 : k)) core (A * C0)
      ((5 : k) • A ^ 3 - (4 : k) • B ^ 2)
      (A.natDegree + C0.natDegree) (by norm_num) (mul_ne_zero hA hC0)
      (by omega) hfaceDeg hrest heqCore).elim

/-- Leading equation of a constant cubic core on its balanced positive
degree chamber. -/
theorem noncubicBeta_constantCore_balanced_leadingCoeff
    (A B C0 : k[X]) (hA : A ≠ 0) (hC0 : C0 ≠ 0)
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hcore0 : (betaOneCorePolynomial410 A B C0).natDegree = 0) :
    (5 : k) * A.leadingCoeff ^ 3 -
        24 * (A.leadingCoeff * C0.leadingCoeff) = 0 := by
  have hA3deg : (A ^ 3).natDegree = 3 * A.natDegree := by
    rw [natDegree_pow]
  have hACdeg : (A * C0).natDegree = 3 * A.natDegree := by
    rw [natDegree_mul hA hC0, hbalanced]
    omega
  have hB2deg : (B ^ 2).natDegree < 3 * A.natDegree := by
    rw [natDegree_pow, hB0]
    omega
  have hCoredeg :
      (betaOneCorePolynomial410 A B C0).natDegree <
        3 * A.natDegree := by omega
  have hA3coeff : (A ^ 3).coeff (3 * A.natDegree) =
      A.leadingCoeff ^ 3 := by
    rw [← hA3deg, coeff_natDegree, leadingCoeff_pow]
  have hACcoeff : (A * C0).coeff (3 * A.natDegree) =
      A.leadingCoeff * C0.leadingCoeff := by
    rw [← hACdeg, coeff_natDegree, leadingCoeff_mul]
  have hcoeff :
      (betaOneCorePolynomial410 A B C0).coeff (3 * A.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hCoredeg
  simp only [betaOneCorePolynomial410, coeff_sub, coeff_smul,
    hA3coeff, hACcoeff, coeff_eq_zero_of_natDegree_lt hB2deg,
    smul_eq_mul, mul_zero, sub_zero] at hcoeff
  exact hcoeff

/-- The omitted terms below the balanced positive-degree `I1` face,
including the genuine nonzero beta contribution. -/
def noncubicBetaBalancedOneRest410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  betaCubicBalancedStrictOneRest410 gamma delta zeta eta theta A B C0 +
    betaLoadOnePolynomial410 beta A B C0

theorem firstIntegralOne410_eq_noncubicBalancedFace_add_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    firstIntegralOnePolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      betaCubicBalancedStrictOneFace410 A C0 +
        noncubicBetaBalancedOneRest410
          beta gamma delta zeta eta theta A B C0 := by
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionOnePolynomial410_eq_beta_add_rest, zeroLoadOne410_eq]
  simp only [betaCubicBalancedStrictOneFace410,
    betaCubicBalancedStrictOneRest410, noncubicBetaBalancedOneRest410]
  abel

theorem noncubicBetaBalancedOneRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree) :
    (noncubicBetaBalancedOneRest410
      beta gamma delta zeta eta theta A B C0).natDegree <
        6 * A.natDegree := by
  simp only [noncubicBetaBalancedOneRest410,
    betaCubicBalancedStrictOneRest410, betaLoadOnePolynomial410,
    betaLoadOneRest410]
  compute_degree
  omega

theorem noncubicBeta_degreeZero_positiveA_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hcore0 : (betaOneCorePolynomial410 A B C0).natDegree = 0)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hbalanced := noncubicBeta_constantCore_balanced
    A B C0 hApos hB0 hcore0
  have hC0 : C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hbalanced
    omega
  have hshape := noncubicBeta_constantCore_balanced_leadingCoeff
    A B C0 hA hC0 hApos hB0 hbalanced hcore0
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
  have hrest := noncubicBetaBalancedOneRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hApos hB0 hbalanced
  have hk1 : (C k1 : k[X]).coeff (6 * A.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  rw [firstIntegralOne410_eq_noncubicBalancedFace_add_rest] at hOne
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

/-! ## Complete component deletion and packet refinement -/

theorem noncubicBeta_degreeZero_component_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k1 terminal : k)
    (A B C0 : k[X])
    (hB0 : B.natDegree = 0)
    (hcore0 : (betaOneCorePolynomial410 A B C0).natDegree = 0)
    (hterminal : terminal ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  by_cases hApos : 0 < A.natDegree
  · exact noncubicBeta_degreeZero_positiveA_impossible
      beta gamma delta zeta eta theta k1 A B C0 hApos hB0 hcore0 hOne
  · have hA0 : A.natDegree = 0 := by omega
    by_cases hCpos : 0 < C0.natDegree
    · exact noncubicBeta_degreeZero_constantA_C_positive_impossible
        beta gamma delta zeta eta theta k1 A B C0 hA0 hB0 hCpos hOne
    · exact betaCubicWall_balanced_constants_impossible
        alpha beta gamma delta epsilon zeta eta theta iota terminal
          A B C0 hA0 hB0 (by omega) hterminal hLower

/-- Genuine beta packet after deleting both the cubic wall and the exact
degree-zero `I1` component. -/
def PositiveNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (betaTwoCorePolynomial410 A B C0 = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree) ∧
    betaOneCorePolynomial410 A B C0 ≠ 0 ∧
      0 < B.natDegree +
        (betaOneCorePolynomial410 A B C0).natDegree ∧
      B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree

def DegreeZeroDeletedEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      PositiveNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_degreeZeroDeleted_earlyLoad_residual
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
      DegreeZeroDeletedEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_cubicDeleted_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    refine ⟨hbeta.1, hbeta.2.1, hbeta.2.2.1, hbeta.2.2.2.1, ?_⟩
    rcases hbeta.2.2.2.2 with hzero | hbound
    · have hOne0 : firstIntegralOnePolynomial410
          0 beta gamma delta zeta eta theta A B C0 = C k1 := by
        simpa [hold.1] using hOne
      have hLower0 : lowerRowZeroPolynomial410
          (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
            A B C0)
          (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
            iota A B C0) B C0 = C terminal := by
        simpa [hold.1] using hLower
      exact (noncubicBeta_degreeZero_component_impossible
        alpha beta gamma delta epsilon zeta eta theta iota k1 terminal
          A B C0 hzero.1 hzero.2 hterminal hOne0 hLower0).elim
    · exact ⟨by
        by_contra hnot
        have hzero : B.natDegree = 0 ∧
            (betaOneCorePolynomial410 A B C0).natDegree = 0 := by omega
        have hOne0 : firstIntegralOnePolynomial410
            0 beta gamma delta zeta eta theta A B C0 = C k1 := by
          simpa [hold.1] using hOne
        have hLower0 : lowerRowZeroPolynomial410
            (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta
              theta A B C0)
            (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta
              eta iota A B C0) B C0 = C terminal := by
          simpa [hold.1] using hLower
        exact noncubicBeta_degreeZero_component_impossible
          alpha beta gamma delta epsilon zeta eta theta iota k1 terminal
            A B C0 hzero.1 hzero.2 hterminal hOne0 hLower0,
        hbound⟩
  · exact Or.inr hlater

theorem integrated410_degreeZeroDeleted_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      DegreeZeroDeletedEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_degreeZeroDeleted_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_degreeZeroDeleted_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          DegreeZeroDeletedEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_degreeZeroDeleted_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end NoncubicBetaDegreeZero410

end Max11DegreeRoutes
