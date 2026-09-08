import LowScale410ScaleZeroGammaOffTieEnvelopeFan

/-!
# Deletion of `A = 0` and collapse of the gamma off-tie fan

On `A = 0`, the first invariant forces the degree tie `4 b = 3 u`.
The exact terminal primitive then has the uniquely dominant face `B^3 U`,
contradicting its forced degree one.  After deleting this coordinate leaf,
all four load strata collapse to five positive-degree cones, with the honest
one-coordinate-constant boundaries retained separately.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaAZeroAndCollapsedFan410

variable {k : Type*} [Field k] [CharZero k]

def gammaAZeroInvariantOneRest410
    (gamma delta eta theta : k) (B U : k[X]) : k[X] :=
  (-(640 * delta) : k) • (B * U) + (2048 * theta : k) • B +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_gamma_A_zero_decomposition
    (gamma delta zeta eta theta : k) (B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta 0 B U =
      (-(320 : k)) • B ^ 4 + (-(40 : k)) • U ^ 3 +
        gammaAZeroInvariantOneRest410 gamma delta eta theta B U := by
  simp [discriminantInvariantOneNumerator410,
    gammaAZeroInvariantOneRest410]
  module

def gammaAZeroTerminalPrimitive410
    (gamma delta zeta theta : k) (B U : k[X]) : k[X] :=
  (1280 : k) • (B ^ 3 * U) - (2048 * gamma : k) • B ^ 3 -
    (3072 * zeta : k) • B ^ 2 + (320 * delta : k) • U ^ 2 -
    (2048 * theta : k) • U

theorem lWallTerminal410_gamma_A_zero_eq_derivative
    (gamma delta zeta eta theta : k) (B U : k[X]) :
    lWallTerminalNumerator410 0 0 gamma delta zeta eta theta 0 B U =
      derivative (gammaAZeroTerminalPrimitive410
        gamma delta zeta theta B U) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    gammaAZeroTerminalPrimitive410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_smul,
    Polynomial.derivative_C, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [zero_mul, mul_zero, zero_smul, add_zero, sub_zero, neg_zero,
    map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gamma_A_zero_discriminant_impossible
    (gamma delta zeta eta theta q1 terminal : k) (B U : k[X])
    (hterminal : terminal ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta 0 B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta 0 B U = C terminal) : False := by
  have hDerivative : derivative
      (gammaAZeroTerminalPrimitive410 gamma delta zeta theta B U) =
        C terminal := by
    rw [← lWallTerminal410_gamma_A_zero_eq_derivative]
    exact hTerminal
  have hDegree : (gammaAZeroTerminalPrimitive410
      gamma delta zeta theta B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaAZeroTerminalPrimitive410 gamma delta zeta theta B U)
      terminal hterminal hDerivative
  have hpositive : 0 < B.natDegree ∨ 0 < U.natDegree := by
    by_contra hnone
    push_neg at hnone
    have hle : (gammaAZeroTerminalPrimitive410
        gamma delta zeta theta B U).natDegree ≤ 0 := by
      simp only [gammaAZeroTerminalPrimitive410]
      compute_degree
      omega
    omega
  rw [discriminantInvariantOne410_gamma_A_zero_decomposition] at hOne
  have hdegree : 4 * B.natDegree = 3 * U.natDegree := by
    rcases lt_trichotomy (4 * B.natDegree) (3 * U.natDegree) with
        hlow | heq | hhigh
    · let R : k[X] := (-(320 : k)) • B ^ 4 +
          gammaAZeroInvariantOneRest410 gamma delta eta theta B U
      have hform : (-(40 : k)) • U ^ 3 + R = C q1 := by
        dsimp only [R]
        linear_combination hOne
      have hrest : R.natDegree < 3 * U.natDegree := by
        dsimp only [R]
        simp only [gammaAZeroInvariantOneRest410]
        compute_degree
        omega
      exfalso
      exact (smul_add_lower_ne_C410 (-(40 : k)) q1 (U ^ 3) R
        (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hU) (by omega)
        (by rw [natDegree_pow]) hrest) hform
    · exact heq
    · let R : k[X] := (-(40 : k)) • U ^ 3 +
          gammaAZeroInvariantOneRest410 gamma delta eta theta B U
      have hform : (-(320 : k)) • B ^ 4 + R = C q1 := by
        dsimp only [R]
        linear_combination hOne
      have hrest : R.natDegree < 4 * B.natDegree := by
        dsimp only [R]
        simp only [gammaAZeroInvariantOneRest410]
        compute_degree
        omega
      exfalso
      exact (smul_add_lower_ne_C410 (-(320 : k)) q1 (B ^ 4) R
        (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB) (by omega)
        (by rw [natDegree_pow]) hrest) hform
  have hBpos : 0 < B.natDegree := by omega
  have hUpos : 0 < U.natDegree := by omega
  let R : k[X] := -(2048 * gamma : k) • B ^ 3 -
    (3072 * zeta : k) • B ^ 2 + (320 * delta : k) • U ^ 2 -
    (2048 * theta : k) • U
  have hform : gammaAZeroTerminalPrimitive410 gamma delta zeta theta B U =
      (1280 : k) • (B ^ 3 * U) + R := by
    dsimp only [R]
    simp only [gammaAZeroTerminalPrimitive410]
    module
  have hrest : R.natDegree < 3 * B.natDegree + U.natDegree := by
    dsimp only [R]
    compute_degree
    omega
  have hmain : ((1280 : k) • (B ^ 3 * U)).natDegree =
      3 * B.natDegree + U.natDegree := by
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  have hfull : (gammaAZeroTerminalPrimitive410
      gamma delta zeta theta B U).natDegree =
        3 * B.natDegree + U.natDegree := by
    rw [hform, natDegree_add_eq_left_of_natDegree_lt]
    · exact hmain
    · rw [hmain]
      exact hrest
  omega

def GammaCollapsedPositiveOffTieCones410 (A B U : k[X]) : Prop :=
  A.natDegree + 2 * B.natDegree ≤ U.natDegree ∨
    3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree ∨
    2 * U.natDegree ≤ B.natDegree

def GammaCollapsedOffTieSelector410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧
    ((B.natDegree = 0 ∨ U.natDegree = 0) ∨
      (0 < B.natDegree ∧ 0 < U.natDegree ∧
        GammaCollapsedPositiveOffTieCones410 A B U))

theorem gamma_exactOffTieFan_A_deleted_collapse
    (delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0)
    (hold : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U) :
    GammaCollapsedOffTieSelector410 A B U := by
  refine ⟨hA, ?_⟩
  by_cases hB0 : B.natDegree = 0
  · exact Or.inl (Or.inl hB0)
  by_cases hU0 : U.natDegree = 0
  · exact Or.inl (Or.inr hU0)
  right
  refine ⟨by omega, by omega, ?_⟩
  rcases hold with hdelta | hzeta | htheta | hbase
  · simp only [GammaDeltaOffTieDegreeFan410] at hdelta
    simp only [GammaCollapsedPositiveOffTieCones410]
    rcases hdelta.2 with hAzero | hfan
    · exact (hA hAzero).elim
    · omega
  · simp only [GammaZetaOffTieDegreeFan410] at hzeta
    simp only [GammaCollapsedPositiveOffTieCones410]
    rcases hzeta.2.2 with hAzero | hfan
    · exact (hA hAzero).elim
    · omega
  · simp only [GammaThetaOffTieDegreeFan410] at htheta
    simp only [GammaCollapsedPositiveOffTieCones410]
    rcases htheta.2.2.2 with hAzero | hfan
    · exact (hA hAzero).elim
    · omega
  · simp only [GammaBaseOffTieDegreeFan410] at hbase
    simp only [GammaCollapsedPositiveOffTieCones410]
    rcases hbase.2.2.2.2 with hAzero | hfan
    · exact (hA hAzero).elim
    · omega

def ADeletedCollapsedFanGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaCollapsedOffTieSelector410 A B (A ^ 2 - (4 : k) • C0)

theorem exactOffTieFan_A_deleted_collapse_refinement
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hA : A ≠ 0)
    (hold : ExactOffTieFanGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    ADeletedCollapsedFanGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 :=
  ⟨hold.1, gamma_exactOffTieFan_A_deleted_collapse
    delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) hA hold.2⟩

def ADeletedCollapsedFanNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    ADeletedCollapsedFanGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_A_deletedCollapsedFanNoncubic_residual
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
    l = 0 ∧ ADeletedCollapsedFanNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_exactOffTieFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hOne0 : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1 := by
    simpa [hold.1, hold.2.1] using hOne
  have hLower0 : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal := by
    simpa [hold.1, hold.2.1] using hLower
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C (8192 * terminal) := by
    dsimp only [U]
    rw [← lowerRow410_discriminantTerminalNumerator, hLower0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hdesc := hold.2.2.2.2.1
  have hB : B ≠ 0 := hdesc.1.1.1.1.1.1.1.1.2
  have hU : U ≠ 0 := hdesc.1.1.1.1.1.1.1.1.1.2
  have hA : A ≠ 0 := by
    intro hAzero
    subst A
    exact gamma_A_zero_discriminant_impossible
      gamma delta zeta eta theta (2048 * k1) (8192 * terminal) B U
        (mul_ne_zero (by norm_num) hterminal) hB hU hOneD hTerminalD
  exact ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1,
    exactOffTieFan_A_deleted_collapse_refinement
      gamma delta zeta eta theta A B C0 hA hold.2.2.2.2⟩

theorem integrated410_A_deletedCollapsedFanNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ ADeletedCollapsedFanNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_A_deletedCollapsedFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_A_deletedCollapsedFanNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        ADeletedCollapsedFanNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_A_deletedCollapsedFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaAZeroAndCollapsedFan410

end Max11DegreeRoutes
