import LowScale410ScaleZeroGammaBZeroElimination

/-!
# Deletion of the `deg B = deg U = 0` gamma endpoint

With nonzero constant `B` and `U`, positive-degree `A` is excluded by a
three-step load split.  Delta exposes `A^2 B`; after delta vanishes, zeta
exposes `A^2`; after both vanish, the linear `I2` coefficient and the top
terminal coefficient are incompatible.  The argument is independent of
gamma nonvanishing.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaBUConstantEndpoint410

variable {k : Type*} [Field k] [CharZero k]

def gammaBUConstantI1DeltaRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (960 : k) • (A * B ^ 2 * U) -
    (1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (320 : k) • B ^ 4 -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B -
    (40 : k) • U ^ 3 + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantOne410_eq_BUconstant_delta_face_add_rest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(320 * delta : k)) • (A ^ 2 * B) +
        gammaBUConstantI1DeltaRest410
          gamma delta zeta eta theta A B U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantOneNumerator410,
    gammaBUConstantI1DeltaRest410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

def gammaBUConstantI2ZetaRest410
    (gamma zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(1280 : k) • (A * B ^ 3) + (2048 * theta : k) • A +
    (480 : k) • (B * U ^ 2) - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B - (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_delta_zero_eq_BUconstant_zeta_face_add_rest
    (gamma zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma 0 zeta eta theta A B U =
      (768 * zeta : k) • A ^ 2 +
        gammaBUConstantI2ZetaRest410 gamma zeta eta theta A B U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantTwoNumerator410,
    gammaBUConstantI2ZetaRest410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

def gammaBUConstantI2LinearRest410
    (gamma eta : k) (B U : k[X]) : k[X] :=
  (480 : k) • (B * U ^ 2) - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B

theorem discriminantInvariantTwo410_delta_zeta_zero_eq_BUconstant_linear
    (gamma eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma 0 0 eta theta A B U =
      (-(1280 : k)) • (A * B ^ 3) +
        (2048 * theta : k) • A +
          gammaBUConstantI2LinearRest410 gamma eta B U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantTwoNumerator410,
    gammaBUConstantI2LinearRest410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

def gammaBUConstantTerminalRest410
    (gamma eta : k) (B U : k[X]) (A : k[X]) : k[X] :=
  ((-(480 : k)) • (B * U ^ 2) +
      (1536 * gamma : k) • (B * U) - (4096 * eta : k) • B) *
    derivative A

theorem lWallTerminal410_delta_zeta_zero_BUconstant_decomposition
    (gamma eta theta : k) (A B U : k[X])
    (hB0 : B.natDegree = 0) (hU0 : U.natDegree = 0) :
    lWallTerminalNumerator410 0 0 gamma 0 0 eta theta A B U =
      (1280 : k) • (A * B ^ 3 * derivative A) +
        (4096 * theta : k) • (A * derivative A) +
          gammaBUConstantTerminalRest410 gamma eta B U A := by
  have hdB : derivative B = 0 := derivative_eq_zero.mpr hB0
  have hdU : derivative U = 0 := derivative_eq_zero.mpr hU0
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    gammaBUConstantTerminalRest410, hdB, hdU,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gamma_BU_constant_endpoint_discriminant_impossible
    (gamma delta zeta eta theta k2 k1 terminal : k) (A B U : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hU0 : U.natDegree = 0) (hB : B ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal) : False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  by_cases hdelta : delta = 0
  · subst delta
    by_cases hzeta : zeta = 0
    · subst zeta
      rw [discriminantInvariantTwo410_delta_zeta_zero_eq_BUconstant_linear]
        at hTwo
      rw [lWallTerminal410_delta_zeta_zero_BUconstant_decomposition
        gamma eta theta A B U hB0 hU0] at hTerminal
      have hAB3deg : (A * B ^ 3).natDegree = A.natDegree := by
        rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow, hB0]
        omega
      have hI2rest :
          (gammaBUConstantI2LinearRest410 gamma eta B U).natDegree <
            A.natDegree := by
        simp only [gammaBUConstantI2LinearRest410]
        compute_degree
        omega
      have hI2coeff := congrArg
        (fun P : k[X] => P.coeff A.natDegree) hTwo
      rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
        show (A * B ^ 3).coeff A.natDegree =
            A.leadingCoeff * B.leadingCoeff ^ 3 by
          rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul,
            leadingCoeff_pow],
        show A.coeff A.natDegree = A.leadingCoeff by rw [coeff_natDegree],
        coeff_eq_zero_of_natDegree_lt hI2rest, add_zero,
        show (C k2 : k[X]).coeff A.natDegree = 0 by
          apply coeff_eq_zero_of_natDegree_lt
          rw [natDegree_C]
          omega] at hI2coeff
      simp only [smul_eq_mul] at hI2coeff
      have hthetaCore :
          -(1280 : k) * B.leadingCoeff ^ 3 + 2048 * theta = 0 := by
        apply (mul_left_cancel₀ hAlc)
        linear_combination hI2coeff
      have hAdegne : A.natDegree ≠ 0 := by omega
      have hdA : derivative A ≠ 0 := derivative_ne_zero.mpr hAdegne
      have hAB3ddeg : (A * B ^ 3 * derivative A).natDegree =
          2 * A.natDegree - 1 := by
        rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 3 hB)) hdA,
          natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow,
          natDegree_derivative, hB0]
        omega
      have hAddeg : (A * derivative A).natDegree =
          2 * A.natDegree - 1 := by
        rw [natDegree_mul hA hdA, natDegree_derivative]
        omega
      have hTerminalRest :
          (gammaBUConstantTerminalRest410 gamma eta B U A).natDegree <
            2 * A.natDegree - 1 := by
        simp only [gammaBUConstantTerminalRest410]
        compute_degree
        omega
      have hTerminalCoeff := congrArg
        (fun P : k[X] => P.coeff (2 * A.natDegree - 1)) hTerminal
      rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
        show (A * B ^ 3 * derivative A).coeff
            (2 * A.natDegree - 1) =
              (A.leadingCoeff * B.leadingCoeff ^ 3) *
                (A.leadingCoeff * (A.natDegree : ℕ)) by
          rw [← hAB3ddeg, coeff_natDegree, leadingCoeff_mul,
            leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_derivative],
        show (A * derivative A).coeff (2 * A.natDegree - 1) =
            A.leadingCoeff *
              (A.leadingCoeff * (A.natDegree : ℕ)) by
          rw [← hAddeg, coeff_natDegree, leadingCoeff_mul,
            leadingCoeff_derivative],
        coeff_eq_zero_of_natDegree_lt hTerminalRest, add_zero,
        show (C terminal : k[X]).coeff (2 * A.natDegree - 1) = 0 by
          apply coeff_eq_zero_of_natDegree_lt
          rw [natDegree_C]
          omega] at hTerminalCoeff
      simp only [smul_eq_mul] at hTerminalCoeff
      have hncast : (A.natDegree : k) ≠ 0 := by
        exact_mod_cast hAdegne
      have hTerminalCore :
          1280 * B.leadingCoeff ^ 3 + 4096 * theta = 0 := by
        apply (mul_left_cancel₀
          (mul_ne_zero (pow_ne_zero 2 hAlc) hncast))
        linear_combination hTerminalCoeff
      have hzero : (3840 : k) * B.leadingCoeff ^ 3 = 0 := by
        linear_combination hTerminalCore - (2 : k) * hthetaCore
      exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hBlc)) hzero
    · rw [discriminantInvariantTwo410_delta_zero_eq_BUconstant_zeta_face_add_rest]
        at hTwo
      have hrest :
          (gammaBUConstantI2ZetaRest410
            gamma zeta eta theta A B U).natDegree < 2 * A.natDegree := by
        simp only [gammaBUConstantI2ZetaRest410]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (768 * zeta : k) k2 (A ^ 2)
        (gammaBUConstantI2ZetaRest410 gamma zeta eta theta A B U)
        (2 * A.natDegree) (mul_ne_zero (by norm_num) hzeta)
        (pow_ne_zero 2 hA) (by omega) (by rw [natDegree_pow]) hrest) hTwo
  · rw [discriminantInvariantOne410_eq_BUconstant_delta_face_add_rest]
      at hOne
    have hrest : (gammaBUConstantI1DeltaRest410
        gamma delta zeta eta theta A B U).natDegree <
          2 * A.natDegree := by
      simp only [gammaBUConstantI1DeltaRest410]
      compute_degree
      omega
    have hmain : (A ^ 2 * B).natDegree = 2 * A.natDegree := by
      rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow, hB0]
      omega
    exact (smul_add_lower_ne_C410 (-(320 * delta : k)) k1 (A ^ 2 * B)
      (gammaBUConstantI1DeltaRest410 gamma delta zeta eta theta A B U)
      (2 * A.natDegree) (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
      (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hmain hrest) hOne

def BUConstantEndpointDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  BZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    ¬ (B.natDegree = 0 ∧
      (A ^ 2 - (4 : k) • C0).natDegree = 0)

theorem BZeroDeletedGammaNewtonResidual410_BUconstant_refinement
    (alpha gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hold : BZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    BUConstantEndpointDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  rintro ⟨hB0, hU0⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hApos : 0 < A.natDegree := by
    by_contra hnot
    have hA0 : A.natDegree = 0 := by omega
    have hCU : (4 : k) • C0 = A ^ 2 - U := by
      dsimp only [U]
      module
    have hC0 : C0.natDegree = 0 := by
      have hle : C0.natDegree ≤ max (A ^ 2).natDegree U.natDegree := by
        rw [← natDegree_smul C0 (by norm_num : (4 : k) ≠ 0), hCU]
        exact natDegree_sub_le _ _
      rw [natDegree_pow, hA0, hU0] at hle
      omega
    exact betaCubicWall_balanced_constants_impossible
      alpha 0 gamma delta epsilon zeta eta theta iota terminal
        A B C0 hA0 hB0 hC0 hterminal hLower
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C (8192 * terminal) := by
    dsimp only [U]
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact gamma_BU_constant_endpoint_discriminant_impossible
    gamma delta zeta eta theta (2048 * k2) (2048 * k1)
      (8192 * terminal) A B U hApos hB0 (by simpa only [U] using hU0)
      hold.2 hTwoD hOneD hTerminalD

/-! ## Source-facing endpoint deletion -/

def GammaBUConstantEndpointDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      BUConstantEndpointDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaBUConstantEndpointDeletedNoncubic_residual
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
      GammaBUConstantEndpointDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaBZeroDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
          iota A B C0) B C0 = C terminal := by
      simpa [hold.1, hgamma.1] using hLower
    left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      BZeroDeletedGammaNewtonResidual410_BUconstant_refinement
        alpha gamma delta epsilon zeta eta theta iota k2 k1 terminal
          A B C0 hterminal hTwo0 hOne0 hLower0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaBUConstantEndpointDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaBUConstantEndpointDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaBUConstantEndpointDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaBUConstantEndpointDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaBUConstantEndpointDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaBUConstantEndpointDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaBUConstantEndpoint410

end Max11DegreeRoutes
