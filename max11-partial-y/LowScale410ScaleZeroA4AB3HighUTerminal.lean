import LowScale410ScaleZeroA4AB3EqualUTerminal

/-!
# Terminal elimination of the `2u=3a` `A^4 = A B^3` wall

On the sole remaining component of the first triangle branch one has
`a=b>0` and `2u=3a`.  The top `I2` face is

`140 beta A^4 - 1280 A B^3 + 480 B U^2`,

while the terminal numerator has top face

`(1120 beta A^4 + 1280 A B^3 - 480 B U^2) A'`.

Their leading equations add to a nonzero multiple of
`beta lc(A)^4`.  Hence the entire first triangle branch is empty.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section A4AB3HighUTerminal410

variable {k : Type*} [Field k] [CharZero k]

def scaleZeroA4AB3BU2RestTwo410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 - (336 * beta : k) • (A ^ 2 * U) +
    (768 * zeta : k) • A ^ 2 - (1344 * beta : k) • (A * B ^ 2) -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A +
    (1280 * delta : k) • B ^ 2 - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B + (336 * beta : k) • U ^ 2 -
    (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_eq_A4AB3BU2_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 beta gamma delta zeta eta theta A B U =
      (140 * beta : k) • A ^ 4 + (-(1280 : k)) • (A * B ^ 3) +
        (480 : k) • (B * U ^ 2) +
          scaleZeroA4AB3BU2RestTwo410
            beta gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantTwoNumerator410,
    scaleZeroA4AB3BU2RestTwo410]
  module

def scaleZeroHighUTerminalARest410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (1920 * delta : k) • A ^ 3 - (1344 * beta : k) • (A ^ 2 * U) +
    (3072 * zeta : k) • A ^ 2 - (1280 * delta : k) • (A * U) +
    (4096 * theta : k) • A - (2560 * delta : k) • B ^ 2 +
    (1536 * gamma : k) • (B * U) - (4096 * eta : k) • B

def scaleZeroHighUTerminalRest410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  scaleZeroHighUTerminalARest410 beta gamma delta zeta eta theta A B U *
      derivative A +
    lWallTerminalBCoefficient410 0 beta gamma delta zeta A B U *
      derivative B +
    lWallTerminalUCoefficient410 0 beta delta zeta theta A B U *
      derivative U

theorem lWallTerminalNumerator410_eq_highU_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 beta gamma delta zeta eta theta A B U =
      (1120 * beta : k) • (A ^ 4 * derivative A) +
        (1280 : k) • (A * B ^ 3 * derivative A) +
        (-(480 : k)) • (B * U ^ 2 * derivative A) +
          scaleZeroHighUTerminalRest410
            beta gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    scaleZeroHighUTerminalRest410, scaleZeroHighUTerminalARest410,
    zero_mul, mul_zero, zero_smul, zero_add, add_zero, neg_zero,
    add_mul, sub_mul, smul_mul_assoc]
  module

theorem scaleZeroA4AB3BU2RestTwo410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUtop : 2 * U.natDegree = 3 * A.natDegree) :
    (scaleZeroA4AB3BU2RestTwo410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [scaleZeroA4AB3BU2RestTwo410]
  compute_degree
  omega

theorem scaleZeroHighUTerminalRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUtop : 2 * U.natDegree = 3 * A.natDegree) :
    (scaleZeroHighUTerminalRest410
      beta gamma delta zeta eta theta A B U).natDegree <
        5 * A.natDegree - 1 := by
  simp only [scaleZeroHighUTerminalRest410,
    scaleZeroHighUTerminalARest410, lWallTerminalBCoefficient410,
    lWallTerminalUCoefficient410, zero_mul, mul_zero, zero_smul,
    zero_add, add_zero, neg_zero]
  compute_degree
  omega

/-- The `2u=3a` component has incompatible `I2` and terminal top faces. -/
theorem scaleZero_positiveBeta_A4AB3_highU_terminal_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X]) (hbeta : beta ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUtop : 2 * (A ^ 2 - (4 : k) • C0).natDegree =
      3 * A.natDegree)
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
  have hUdeg : 2 * U.natDegree = 3 * A.natDegree := by
    simpa only [U] using hUtop
  have hUpos : 0 < U.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUpos
    omega
  have hAdegne : A.natDegree ≠ 0 := by omega
  have hdA : derivative A ≠ 0 := derivative_ne_zero.mpr hAdegne
  have hrestTwo := scaleZeroA4AB3BU2RestTwo410_natDegree_lt
    beta gamma delta zeta eta theta A B U hBpos hTie hUdeg
  have hrestTerminal := scaleZeroHighUTerminalRest410_natDegree_lt
    beta gamma delta zeta eta theta A B U hBpos hTie hUdeg
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
  rw [discriminantInvariantTwo410_eq_A4AB3BU2_face_add_rest] at hTwoD
  rw [lWallTerminalNumerator410_eq_highU_face_add_rest] at hTerminalD
  have hA4deg : (A ^ 4).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow]
  have hAB3deg : (A * B ^ 3).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow, hABdeg]
    omega
  have hBU2deg : (B * U ^ 2).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow, hABdeg]
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
  have hBU2ddeg : (B * U ^ 2 * derivative A).natDegree =
      5 * A.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero hB (pow_ne_zero 2 hU)) hdA,
      natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow,
      natDegree_derivative, hABdeg]
    omega
  have hTwoCoeff := congrArg
    (fun P : k[X] => P.coeff (4 * A.natDegree)) hTwoD
  rw [coeff_add, coeff_add, coeff_add, coeff_smul, coeff_smul, coeff_smul,
    show (A ^ 4).coeff (4 * A.natDegree) = A.leadingCoeff ^ 4 by
      rw [← hA4deg, coeff_natDegree, leadingCoeff_pow],
    show (A * B ^ 3).coeff (4 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff (4 * A.natDegree) =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hrestTwo, add_zero,
    show (C (2048 * k2) : k[X]).coeff (4 * A.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hTerminalCoeff := congrArg
    (fun P : k[X] => P.coeff (5 * A.natDegree - 1)) hTerminalD
  rw [coeff_add, coeff_add, coeff_add, coeff_smul, coeff_smul, coeff_smul,
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
    show (B * U ^ 2 * derivative A).coeff (5 * A.natDegree - 1) =
        (B.leadingCoeff * U.leadingCoeff ^ 2) *
          (A.leadingCoeff * (A.natDegree : ℕ)) by
      rw [← hBU2ddeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_derivative],
    coeff_eq_zero_of_natDegree_lt hrestTerminal, add_zero,
    show (C (8192 * terminal) : k[X]).coeff
        (5 * A.natDegree - 1) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTerminalCoeff
  simp only [smul_eq_mul] at hTerminalCoeff
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hncast : (A.natDegree : k) ≠ 0 := by
    exact_mod_cast hAdegne
  have hTwoFace :
      140 * beta * A.leadingCoeff ^ 4 -
          1280 * (A.leadingCoeff * B.leadingCoeff ^ 3) +
        480 * (B.leadingCoeff * U.leadingCoeff ^ 2) = 0 := by
    linear_combination hTwoCoeff
  have hTerminalFace :
      1120 * beta * A.leadingCoeff ^ 4 +
          1280 * (A.leadingCoeff * B.leadingCoeff ^ 3) -
        480 * (B.leadingCoeff * U.leadingCoeff ^ 2) = 0 := by
    apply (mul_left_cancel₀ (mul_ne_zero hAlc hncast))
    linear_combination hTerminalCoeff
  have hzero : (1260 : k) * beta * A.leadingCoeff ^ 4 = 0 := by
    linear_combination hTwoFace + hTerminalFace
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hbeta)
    (pow_ne_zero 4 hAlc)) hzero

def RemainingTwoScaleZeroI2TriangleTie410 (A B U : k[X]) : Prop :=
  (4 * A.natDegree = B.natDegree + 2 * U.natDegree ∧
      A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree) ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree)

theorem scaleZero_positiveBeta_remainingTwo_I2_triangle_classification
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
      RemainingTwoScaleZeroI2TriangleTie410
        A B (A ^ 2 - (4 : k) • C0) := by
  have hold := scaleZero_positiveBeta_terminalRefined_I2_triangle_classification
    alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hbeta hBpos hTwo hOne hLower
  rcases hold with hA | hU | htie
  · exact Or.inl hA
  · exact Or.inr (Or.inl hU)
  · right
    right
    rcases htie with hfirst | hsecond | hthird
    · exact (scaleZero_positiveBeta_A4AB3_highU_terminal_impossible
        alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
          A B C0 hbeta hBpos hfirst.1 hfirst.2.2 hTwo hLower).elim
    · exact Or.inl hsecond
    · exact Or.inr hthird

/-! ## Source-facing two-tie packet -/

def RemainingTwoPositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    (A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      RemainingTwoScaleZeroI2TriangleTie410
        A B (A ^ 2 - (4 : k) • C0))

def RemainingTwoPositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      RemainingTwoPositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_remainingTwoPositiveB_earlyLoad_residual
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
      RemainingTwoPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_terminalRefinedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan, htriangle⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_remainingTwo_I2_triangle_classification
      alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hbeta hfan.1.2.2.2.2
    · simpa [hold.1] using hTwo
    · simpa [hold.1] using hOne
    · simpa [hold.1] using hLower
  · exact Or.inr hlater

theorem integrated410_remainingTwoPositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      RemainingTwoPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_remainingTwoPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_remainingTwoPositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          RemainingTwoPositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_remainingTwoPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end A4AB3HighUTerminal410

end Max11DegreeRoutes
