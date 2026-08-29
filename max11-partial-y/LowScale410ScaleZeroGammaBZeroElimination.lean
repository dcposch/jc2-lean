import LowScale410ScaleZeroGammaUZeroBoundaryElimination

/-!
# Deletion of the entire `B=0` gamma face

In discriminant coordinates, `B=0` makes the second invariant a fixed
cubic in `U`, so constancy forces `deg U=0`.  The first invariant then
successively excludes positive-degree `A` when delta, zeta, or theta is
nonzero; if all three vanish, the terminal row is zero.  Constant `A` is
also terminally impossible.  No hypothesis on gamma or eta is needed.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaBZeroElimination410

variable {k : Type*} [Field k] [CharZero k]

theorem discriminantInvariantOne410_B_zero_specialization
    (gamma delta zeta eta theta : k) (A U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A 0 U =
      (-(40 : k)) • U ^ 3 + (192 * gamma : k) • U ^ 2 -
        (1024 * eta : k) • U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantOneNumerator410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem discriminantInvariantTwo410_B_zero_specialization
    (gamma delta zeta eta theta : k) (A U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A 0 U =
      (320 * delta : k) • A ^ 3 + (768 * zeta : k) • A ^ 2 +
        (2048 * theta : k) • A - (640 * delta : k) • (A * U) -
        (1536 * zeta : k) • U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantTwoNumerator410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gamma_B_zero_discriminant_impossible
    (gamma delta zeta eta theta k2 k1 terminal : k) (A B U : k[X])
    (hB : B = 0) (hterminal : terminal ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C k2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C k1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal) : False := by
  subst B
  rw [discriminantInvariantOne410_B_zero_specialization] at hOne
  rw [discriminantInvariantTwo410_B_zero_specialization] at hTwo
  have hU0 : U.natDegree = 0 := by
    by_contra hnot
    have hUpos : 0 < U.natDegree := by omega
    have hU : U ≠ 0 := by
      intro hzero
      subst U
      exact hnot natDegree_zero
    let R : k[X] :=
      (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U
    have heq : (-(40 : k)) • U ^ 3 + R = C k1 := by
      simpa [R, sub_eq_add_neg, add_assoc] using hOne
    have hrest : R.natDegree < 3 * U.natDegree := by
      dsimp only [R]
      compute_degree
      omega
    exact (smul_add_lower_ne_C410 (-(40 : k)) k1 (U ^ 3) R
      (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hU) (by omega)
      (by rw [natDegree_pow]) hrest) heq
  have hdU : derivative U = 0 := derivative_eq_zero.mpr hU0
  by_cases hA0 : A.natDegree = 0
  · have hdA : derivative A = 0 := derivative_eq_zero.mpr hA0
    have hzero : lWallTerminalNumerator410
        0 0 gamma delta zeta eta theta A 0 U = 0 := by
      simp [lWallTerminalNumerator410, hdA, hdU]
    rw [hzero] at hTerminal
    exact hterminal (C_eq_zero.mp hTerminal.symm)
  · have hApos : 0 < A.natDegree := by omega
    have hA : A ≠ 0 := by
      intro hzero
      subst A
      exact hA0 natDegree_zero
    by_cases hdelta : delta = 0
    · by_cases hzeta : zeta = 0
      · by_cases htheta : theta = 0
        · have hzero : lWallTerminalNumerator410
              0 0 gamma delta zeta eta theta A 0 U = 0 := by
            simp [lWallTerminalNumerator410,
              lWallTerminalACoefficient410, lWallTerminalBCoefficient410,
              lWallTerminalUCoefficient410, hdelta, hzeta, htheta, hdU]
          rw [hzero] at hTerminal
          exact hterminal (C_eq_zero.mp hTerminal.symm)
        · have hlinear : (2048 * theta : k) • A = C k2 := by
            simpa [hdelta, hzeta] using hTwo
          have hdegree := congrArg Polynomial.natDegree hlinear
          rw [natDegree_smul A (mul_ne_zero (by norm_num) htheta),
            natDegree_C] at hdegree
          omega
      · let R : k[X] :=
          (2048 * theta : k) • A - (1536 * zeta : k) • U
        have heq : (768 * zeta : k) • A ^ 2 + R = C k2 := by
          simpa [R, hdelta, sub_eq_add_neg, add_assoc] using hTwo
        have hrest : R.natDegree < 2 * A.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        exact (smul_add_lower_ne_C410 (768 * zeta : k) k2 (A ^ 2) R
          (2 * A.natDegree) (mul_ne_zero (by norm_num) hzeta)
          (pow_ne_zero 2 hA) (by omega) (by rw [natDegree_pow]) hrest) heq
    · let R : k[X] :=
        (768 * zeta : k) • A ^ 2 + (2048 * theta : k) • A -
          (640 * delta : k) • (A * U) - (1536 * zeta : k) • U
      have heq : (320 * delta : k) • A ^ 3 + R = C k2 := by
        simpa [R, sub_eq_add_neg, add_assoc] using hTwo
      have hrest : R.natDegree < 3 * A.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (320 * delta : k) k2 (A ^ 3) R
        (3 * A.natDegree) (mul_ne_zero (by norm_num) hdelta)
        (pow_ne_zero 3 hA) (by omega) (by rw [natDegree_pow]) hrest) heq

theorem gamma_B_zero_original_impossible
    (alpha gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hB : B = 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) = C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) = C (2048 * k1) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact gamma_B_zero_discriminant_impossible gamma delta zeta eta theta
    (2048 * k2) (2048 * k1) (8192 * terminal) A B
      (A ^ 2 - (4 : k) • C0) hB (mul_ne_zero (by norm_num) hterminal)
      hTwoD hOneD hTerminalD

def BZeroDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  UZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧ B ≠ 0

theorem UZeroDeletedGammaNewtonResidual410_B_zero_refinement
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
    (hold : UZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    BZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  intro hB
  exact gamma_B_zero_original_impossible
    alpha gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hB hterminal hTwo hOne hLower

/-! ## Source-facing `B=0` deletion -/

def GammaBZeroDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      BZeroDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaBZeroDeletedNoncubic_earlyLoad_residual
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
      GammaBZeroDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaUZeroDeletedNoncubic_earlyLoad_residual
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
      UZeroDeletedGammaNewtonResidual410_B_zero_refinement
        alpha gamma delta epsilon zeta eta theta iota k2 k1 terminal
          A B C0 hterminal hTwo0 hOne0 hLower0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaBZeroDeletedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaBZeroDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaBZeroDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaBZeroDeletedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaBZeroDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaBZeroDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaBZeroElimination410

end Max11DegreeRoutes
