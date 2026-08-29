import LowScale410ScaleZeroA4AB3EqualUTie

/-!
# Terminal elimination of the equal-`U` `A^4 = A B^3` wall

On `a=b=u>0`, the terminal numerator has the unique top differential face

`1120 beta A^4 A' + 1280 A B^3 A'`.

The second invariant has top face

`140 beta A^4 - 1280 A B^3`.

Their leading coefficient equations have nonzero resultant.  Thus the
equal-`U` scalar wall is actually empty, and the first triangle branch is
reduced to the sole degree wall `2u=3a`.  All later loads are retained.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section A4AB3EqualUTerminal410

variable {k : Type*} [Field k] [CharZero k]

def scaleZeroEqualUTerminalARest410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (1920 * delta : k) • A ^ 3 - (1344 * beta : k) • (A ^ 2 * U) +
    (3072 * zeta : k) • A ^ 2 - (1280 * delta : k) • (A * U) +
    (4096 * theta : k) • A - (2560 * delta : k) • B ^ 2 -
    (480 : k) • (B * U ^ 2) + (1536 * gamma : k) • (B * U) -
    (4096 * eta : k) • B

def scaleZeroEqualUTerminalRest410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  scaleZeroEqualUTerminalARest410 beta gamma delta zeta eta theta A B U *
      derivative A +
    lWallTerminalBCoefficient410 0 beta gamma delta zeta A B U *
      derivative B +
    lWallTerminalUCoefficient410 0 beta delta zeta theta A B U *
      derivative U

theorem lWallTerminalNumerator410_eq_equalU_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 beta gamma delta zeta eta theta A B U =
      (1120 * beta : k) • (A ^ 4 * derivative A) +
        (1280 : k) • (A * B ^ 3 * derivative A) +
          scaleZeroEqualUTerminalRest410
            beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    scaleZeroEqualUTerminalRest410, scaleZeroEqualUTerminalARest410,
    zero_mul, mul_zero, zero_smul, zero_add, add_zero, neg_zero,
    add_mul, sub_mul, smul_mul_assoc]
  module

theorem scaleZeroEqualUTerminalRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = A.natDegree)
    (hU : U.natDegree = A.natDegree) :
    (scaleZeroEqualUTerminalRest410
      beta gamma delta zeta eta theta A B U).natDegree <
        5 * A.natDegree - 1 := by
  simp only [scaleZeroEqualUTerminalRest410,
    scaleZeroEqualUTerminalARest410, lWallTerminalBCoefficient410,
    lWallTerminalUCoefficient410, zero_mul, mul_zero, zero_smul,
    zero_add, add_zero, neg_zero]
  compute_degree
  omega

/-- The terminal row deletes the entire equal-`U` component. -/
theorem scaleZero_positiveBeta_A4AB3_equalU_terminal_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X]) (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUeq : (A ^ 2 - (4 : k) • C0).natDegree = A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hApos : 0 < A.natDegree := by omega
  have hABdeg : B.natDegree = A.natDegree := by omega
  have hUdeg : U.natDegree = A.natDegree := by
    simpa only [U] using hUeq
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hAdegne : A.natDegree ≠ 0 := by omega
  have hdA : derivative A ≠ 0 := derivative_ne_zero.mpr hAdegne
  have hrestTwo := scaleZeroA4AB3RestTwo410_natDegree_lt_of_equalU
    beta gamma delta zeta eta theta A B U hBpos hTie hUdeg
  have hrestTerminal := scaleZeroEqualUTerminalRest410_natDegree_lt
    beta gamma delta zeta eta theta A B U hApos hABdeg hUdeg
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 beta gamma delta zeta eta theta A B U = C (8192 * terminal) := by
    dsimp only [U]
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [discriminantInvariantTwo410_eq_A4AB3_face_add_rest] at hTwoD
  rw [lWallTerminalNumerator410_eq_equalU_face_add_rest] at hTerminalD
  have hA4deg : (A ^ 4).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow]
  have hAB3deg : (A * B ^ 3).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow, hABdeg]
    omega
  have hA4ddeg : (A ^ 4 * derivative A).natDegree =
      5 * A.natDegree - 1 := by
    rw [natDegree_mul (pow_ne_zero 4 hA) hdA, natDegree_pow,
      natDegree_derivative]
    omega
  have hAB3ddeg : (A * B ^ 3 * derivative A).natDegree =
      5 * A.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 3 hB)) hdA,
      natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow,
      natDegree_derivative, hABdeg]
    omega
  have hTwoCoeff := congrArg
    (fun P : k[X] => P.coeff (4 * A.natDegree)) hTwoD
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A ^ 4).coeff (4 * A.natDegree) = A.leadingCoeff ^ 4 by
      rw [← hA4deg, coeff_natDegree, leadingCoeff_pow],
    show (A * B ^ 3).coeff (4 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hrestTwo, add_zero,
    show (C (2048 * k2) : k[X]).coeff (4 * A.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hTerminalCoeff := congrArg
    (fun P : k[X] => P.coeff (5 * A.natDegree - 1)) hTerminalD
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A ^ 4 * derivative A).coeff (5 * A.natDegree - 1) =
        A.leadingCoeff ^ 4 *
          (A.leadingCoeff * (A.natDegree : ℕ)) by
      rw [← hA4ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_derivative],
    show (A * B ^ 3 * derivative A).coeff (5 * A.natDegree - 1) =
        (A.leadingCoeff * B.leadingCoeff ^ 3) *
          (A.leadingCoeff * (A.natDegree : ℕ)) by
      rw [← hAB3ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_derivative],
    coeff_eq_zero_of_natDegree_lt hrestTerminal, add_zero,
    show (C (8192 * terminal) : k[X]).coeff
        (5 * A.natDegree - 1) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTerminalCoeff
  simp only [smul_eq_mul] at hTerminalCoeff
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hncast : (A.natDegree : k) ≠ 0 := by
    exact_mod_cast hAdegne
  have hTwoCore :
      140 * beta * A.leadingCoeff ^ 3 - 1280 * B.leadingCoeff ^ 3 = 0 := by
    apply (mul_left_cancel₀ hAlc)
    linear_combination hTwoCoeff
  have hTerminalCore :
      1120 * beta * A.leadingCoeff ^ 3 + 1280 * B.leadingCoeff ^ 3 = 0 := by
    apply (mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 hAlc) hncast))
    linear_combination hTerminalCoeff
  have hzero : (11520 : k) * B.leadingCoeff ^ 3 = 0 := by
    linear_combination hTerminalCore - (8 : k) * hTwoCore
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hBlc)) hzero

def TerminalRefinedScaleZeroI2TriangleTie410 (A B U : k[X]) : Prop :=
  (4 * A.natDegree = A.natDegree + 3 * B.natDegree ∧
      B.natDegree + 2 * U.natDegree ≤ 4 * A.natDegree ∧
      2 * U.natDegree = 3 * A.natDegree) ∨
    (4 * A.natDegree = B.natDegree + 2 * U.natDegree ∧
      A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree) ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree)

theorem scaleZero_positiveBeta_terminalRefined_I2_triangle_classification
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      TerminalRefinedScaleZeroI2TriangleTie410
        A B (A ^ 2 - (4 : k) • C0) := by
  have hold := scaleZero_positiveBeta_equalUScalar_I2_triangle_classification
    beta gamma delta zeta eta theta k2 k1 A B C0 hbeta hBpos hTwo hOne
  rcases hold with hA | hU | htie
  · exact Or.inl hA
  · exact Or.inr (Or.inl hU)
  · right
    right
    rcases htie with hfirst | hsecond | hthird
    · left
      refine ⟨hfirst.1, hfirst.2.1, ?_⟩
      rcases hfirst.2.2 with hequal | htop
      · exact (scaleZero_positiveBeta_A4AB3_equalU_terminal_impossible
          alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
            A B C0 hBpos hfirst.1 hequal.1 hTwo hLower).elim
      · exact htop
    · exact Or.inr (Or.inl hsecond)
    · exact Or.inr (Or.inr hthird)

/-! ## Source-facing terminal-refined packet -/

def TerminalRefinedPositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    (A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      TerminalRefinedScaleZeroI2TriangleTie410
        A B (A ^ 2 - (4 : k) • C0))

def TerminalRefinedPositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      TerminalRefinedPositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_terminalRefinedPositiveB_earlyLoad_residual
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
      TerminalRefinedPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_equalUScalarPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan, htriangle⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_terminalRefined_I2_triangle_classification
      alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hbeta hfan.1.2.2.2.2
    · simpa [hold.1] using hTwo
    · simpa [hold.1] using hOne
    · simpa [hold.1] using hLower
  · exact Or.inr hlater

theorem integrated410_terminalRefinedPositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      TerminalRefinedPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_terminalRefinedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_terminalRefinedPositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          TerminalRefinedPositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_terminalRefinedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end A4AB3EqualUTerminal410

end Max11DegreeRoutes
