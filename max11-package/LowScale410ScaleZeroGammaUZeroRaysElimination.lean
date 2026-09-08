import LowScale410ScaleZeroGammaUZeroCompetition

/-!
# Terminal deletion for both positive-degree `U=0` gamma rays

The `delta=0`, `a=2b` ray has the unique terminal leader
`1280 A B^3 A'`.  On the `delta≠0`, `2a=3b` ray, the two terminal leaders
combine with `lc(B)^3+delta lc(A)^2=0` to leave the nonzero coefficient
`640 delta lc(A)^4 a`.  Thus only coordinate-degree-zero boundaries remain
on `U=0`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaUZeroRaysElimination410

variable {k : Type*} [Field k] [CharZero k]

def gammaUZeroDeltaZeroTerminalRest410
    (gamma zeta eta theta : k) (A B : k[X]) : k[X] :=
  ((3072 * zeta : k) • A ^ 2 + (4096 * theta : k) • A -
      (4096 * eta : k) • B) * derivative A +
    (-(6144 * gamma : k) • B ^ 2 -
      (6144 * zeta : k) • B) * derivative B

theorem lWallTerminal410_gamma_U_zero_delta_zero_decomposition
    (gamma zeta eta theta : k) (A B : k[X]) :
    lWallTerminalNumerator410 0 0 gamma 0 zeta eta theta A B 0 =
      (1280 : k) • (A * B ^ 3 * derivative A) +
        gammaUZeroDeltaZeroTerminalRest410 gamma zeta eta theta A B := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    gammaUZeroDeltaZeroTerminalRest410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gammaUZeroDeltaZeroTerminalRest410_natDegree_lt
    (gamma zeta eta theta : k) (A B : k[X])
    (hApos : 0 < A.natDegree) (hBpos : 0 < B.natDegree)
    (hdegree : A.natDegree = 2 * B.natDegree) :
    (gammaUZeroDeltaZeroTerminalRest410
      gamma zeta eta theta A B).natDegree <
        2 * A.natDegree + 3 * B.natDegree - 1 := by
  simp only [gammaUZeroDeltaZeroTerminalRest410]
  compute_degree
  omega

theorem gamma_U_zero_delta_zero_ray_terminal_impossible
    (gamma zeta eta theta terminal : k) (A B : k[X])
    (hApos : 0 < A.natDegree) (hBpos : 0 < B.natDegree)
    (hdegree : A.natDegree = 2 * B.natDegree)
    (hterminal : terminal ≠ 0)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 zeta eta theta A B 0 = C terminal) : False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hdA : derivative A ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hmain : (A * B ^ 3 * derivative A).natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 3 hB)) hdA,
      natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow,
      natDegree_derivative]
    omega
  have hrest := gammaUZeroDeltaZeroTerminalRest410_natDegree_lt
    gamma zeta eta theta A B hApos hBpos hdegree
  rw [lWallTerminal410_gamma_U_zero_delta_zero_decomposition] at hTerminal
  exact (smul_add_lower_ne_C410 (1280 : k) terminal
    (A * B ^ 3 * derivative A)
    (gammaUZeroDeltaZeroTerminalRest410 gamma zeta eta theta A B)
    (2 * A.natDegree + 3 * B.natDegree - 1) (by norm_num)
    (mul_ne_zero (mul_ne_zero hA (pow_ne_zero 3 hB)) hdA)
    (by omega) hmain hrest) hTerminal

def gammaUZeroDeltaTerminalRest410
    (gamma delta zeta eta theta : k) (A B : k[X]) : k[X] :=
  ((3072 * zeta : k) • A ^ 2 + (4096 * theta : k) • A -
      (2560 * delta : k) • B ^ 2 - (4096 * eta : k) • B) *
      derivative A +
    (-(2560 * delta : k) • (A * B) -
      (6144 * gamma : k) • B ^ 2 -
      (6144 * zeta : k) • B) * derivative B

theorem lWallTerminal410_gamma_U_zero_delta_decomposition
    (gamma delta zeta eta theta : k) (A B : k[X]) :
    lWallTerminalNumerator410 0 0 gamma delta zeta eta theta A B 0 =
      (1920 * delta : k) • (A ^ 3 * derivative A) +
        (1280 : k) • (A * B ^ 3 * derivative A) +
          gammaUZeroDeltaTerminalRest410 gamma delta zeta eta theta A B := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    gammaUZeroDeltaTerminalRest410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gammaUZeroDeltaTerminalRest410_natDegree_lt
    (gamma delta zeta eta theta : k) (A B : k[X])
    (hApos : 0 < A.natDegree) (hBpos : 0 < B.natDegree)
    (hdegree : 2 * A.natDegree = 3 * B.natDegree) :
    (gammaUZeroDeltaTerminalRest410
      gamma delta zeta eta theta A B).natDegree <
        4 * A.natDegree - 1 := by
  simp only [gammaUZeroDeltaTerminalRest410]
  compute_degree
  omega

theorem gamma_U_zero_delta_ray_terminal_impossible
    (gamma delta zeta eta theta terminal : k) (A B : k[X])
    (hdelta : delta ≠ 0) (hApos : 0 < A.natDegree)
    (hBpos : 0 < B.natDegree)
    (hdegree : 2 * A.natDegree = 3 * B.natDegree)
    (hscalar : B.leadingCoeff ^ 3 +
      delta * A.leadingCoeff ^ 2 = 0)
    (hterminal : terminal ≠ 0)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B 0 = C terminal) : False := by
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
  have hA3ddeg : (A ^ 3 * derivative A).natDegree =
      4 * A.natDegree - 1 := by
    rw [natDegree_mul (pow_ne_zero 3 hA) hdA, natDegree_pow,
      natDegree_derivative]
    omega
  have hAB3ddeg : (A * B ^ 3 * derivative A).natDegree =
      4 * A.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 3 hB)) hdA,
      natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow,
      natDegree_derivative]
    omega
  have hrest := gammaUZeroDeltaTerminalRest410_natDegree_lt
    gamma delta zeta eta theta A B hApos hBpos hdegree
  rw [lWallTerminal410_gamma_U_zero_delta_decomposition] at hTerminal
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (4 * A.natDegree - 1)) hTerminal
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A ^ 3 * derivative A).coeff (4 * A.natDegree - 1) =
        A.leadingCoeff ^ 3 *
          (A.leadingCoeff * (A.natDegree : ℕ)) by
      rw [← hA3ddeg, coeff_natDegree, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_derivative],
    show (A * B ^ 3 * derivative A).coeff (4 * A.natDegree - 1) =
        (A.leadingCoeff * B.leadingCoeff ^ 3) *
          (A.leadingCoeff * (A.natDegree : ℕ)) by
      rw [← hAB3ddeg, coeff_natDegree, leadingCoeff_mul,
        leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_derivative],
    coeff_eq_zero_of_natDegree_lt hrest, add_zero,
    show (C terminal : k[X]).coeff (4 * A.natDegree - 1) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  have hncast : (A.natDegree : k) ≠ 0 := by
    exact_mod_cast hAdegne
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hzero : (640 : k) * delta * A.leadingCoeff ^ 4 *
      (A.natDegree : k) = 0 := by
    linear_combination hcoeff -
      (1280 * A.leadingCoeff ^ 2 * (A.natDegree : k)) * hscalar
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hdelta) (pow_ne_zero 4 hAlc))
      hncast) hzero

theorem gamma_U_zero_positiveFan_terminal_impossible
    (alpha gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hfan : GammaUZeroPositiveDegreeFan410 gamma delta A B)
    (hpositive : 0 < A.natDegree ∨ 0 < B.natDegree)
    (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hTerminalD : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [hU] at hTerminalD
  have hterminalD : 8192 * terminal ≠ 0 :=
    mul_ne_zero (by norm_num) hterminal
  rcases hfan with hzero | hdelta
  · exact gamma_U_zero_delta_zero_ray_terminal_impossible
      gamma zeta eta theta (8192 * terminal) A B
        (by omega) (by omega) hzero.2.1 hterminalD
        (by simpa [hzero.1] using hTerminalD)
  · exact gamma_U_zero_delta_ray_terminal_impossible
      gamma delta zeta eta theta (8192 * terminal) A B hdelta.1
        (by omega) (by omega) hdelta.2.1 hdelta.2.2 hterminalD hTerminalD

def UZeroRaysDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  UZeroFanRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    ¬ (A ^ 2 - (4 : k) • C0 = 0 ∧
      GammaUZeroPositiveDegreeFan410 gamma delta A B)

theorem UZeroFanRefinedGammaNewtonResidual410_rays_refinement
    (alpha gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hold : UZeroFanRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    UZeroRaysDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  rintro ⟨hU, hfan⟩
  have hpositive : 0 < A.natDegree ∨ 0 < B.natDegree := by
    by_contra hnone
    push_neg at hnone
    exact hold.1.1.1.2 ⟨hU, by omega, by omega⟩
  exact gamma_U_zero_positiveFan_terminal_impossible
    alpha gamma delta epsilon zeta eta theta iota terminal A B C0
      hU hfan hpositive hterminal hLower

theorem UZeroRaysDeletedGammaNewtonResidual410_zeroU_selector
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hold : UZeroRaysDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    A.natDegree = 0 ∨ B.natDegree = 0 := by
  rcases hold.1.2 with hUne | hfan
  · exact (hUne hU).elim
  · rcases hfan with hA0 | hB0 | hpositive
    · exact Or.inl hA0
    · exact Or.inr hB0
    · exact (hold.2 ⟨hU, hpositive⟩).elim

/-! ## Source-facing refinement -/

def GammaUZeroRaysDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      UZeroRaysDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaUZeroRaysDeletedNoncubic_earlyLoad_residual
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
      GammaUZeroRaysDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaUZeroFanNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
          iota A B C0) B C0 = C terminal := by
      simpa [hold.1, hgamma.1] using hLower
    left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      UZeroFanRefinedGammaNewtonResidual410_rays_refinement
        alpha gamma delta epsilon zeta eta theta iota terminal A B C0
          hterminal hLower0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaUZeroRaysDeletedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaUZeroRaysDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaUZeroRaysDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaUZeroRaysDeletedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaUZeroRaysDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaUZeroRaysDeletedNoncubic_earlyLoad_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaUZeroRaysElimination410

end Max11DegreeRoutes
