import LowScale410ScaleZeroGammaFirstTieCoreRays

/-!
# Elimination for the core-zero fixed-face tie

The two exact rays left by the preceding packet both contradict the constant
second invariant.  On the high-`B` ray the core identity combines the fixed
faces to `2560 A B^3`; on the low-`B` ray the nonzero-delta face `320 delta A^3`
is uniquely dominant.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFirstTieCoreZeroElimination410

variable {k : Type*} [Field k] [CharZero k]

theorem discriminantInvariantTwo410_coreZero_eq_AB3_add_loadRest
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (2560 : k) • (A * B ^ 3) +
        gammaI2LoadRest410 gamma delta zeta eta theta A B U := by
  have hU2 : U ^ 2 = (8 : k) • (A * B ^ 2) := sub_eq_zero.mp hcore
  have hBU2 : B * U ^ 2 = (8 : k) • (A * B ^ 3) := by
    rw [hU2]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest,
    hBU2]
  module

theorem gammaI2LoadRest410_natDegree_lt_AB3_highRay
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hUpos : 0 < U.natDegree) :
    (gammaI2LoadRest410 gamma delta zeta eta theta A B U).natDegree <
      A.natDegree + 3 * B.natDegree := by
  simp only [gammaI2LoadRest410]
  compute_degree
  omega

theorem constantDiscriminantI2_gamma_fixedTie_coreZero_highRay_impossible
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) : False := by
  have hA : A ≠ 0 := by
    intro hAzero
    have hUzero : U ^ 2 = 0 := by simpa [hAzero] using hcore
    exact hU (eq_zero_of_pow_eq_zero hUzero)
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  have hrest := gammaI2LoadRest410_natDegree_lt_AB3_highRay
    gamma delta zeta eta theta A B U hA hB hU htie hray hUpos
  rw [discriminantInvariantTwo410_coreZero_eq_AB3_add_loadRest
    gamma delta zeta eta theta A B U hcore] at hTwo
  have hmain : (A * B ^ 3).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  exact (smul_add_lower_ne_C410 (2560 : k) q (A * B ^ 3)
    (gammaI2LoadRest410 gamma delta zeta eta theta A B U)
    (A.natDegree + 3 * B.natDegree) (by norm_num)
    (mul_ne_zero hA (pow_ne_zero 3 hB)) (by omega) hmain hrest) hTwo

def gammaI2DeltaA3Rest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(1280 : k)) • (A * B ^ 3) + (768 * zeta : k) • A ^ 2 -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A +
    (1280 * delta : k) • B ^ 2 + (480 : k) • (B * U ^ 2) -
    (1536 * gamma : k) • (B * U) + (4096 * eta : k) • B -
    (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_eq_deltaA3_add_rest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (320 * delta : k) • A ^ 3 +
        gammaI2DeltaA3Rest410 gamma delta zeta eta theta A B U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantTwoNumerator410, gammaI2DeltaA3Rest410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gammaI2DeltaA3Rest410_natDegree_lt_A3_lowRay
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 3 * B.natDegree = U.natDegree)
    (hBpos : 0 < B.natDegree) :
    (gammaI2DeltaA3Rest410 gamma delta zeta eta theta A B U).natDegree <
      3 * A.natDegree := by
  simp only [gammaI2DeltaA3Rest410]
  compute_degree
  omega

theorem constantDiscriminantI2_gamma_fixedTie_coreZero_lowRay_impossible
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) : False := by
  have hBpos : 0 < B.natDegree := by
    by_contra hnot
    have hB0 : B.natDegree = 0 := by omega
    have hU0 : U.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  have hApos : 0 < A.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hrest := gammaI2DeltaA3Rest410_natDegree_lt_A3_lowRay
    gamma delta zeta eta theta A B U hA hB hU htie hray.2 hBpos
  rw [discriminantInvariantTwo410_eq_deltaA3_add_rest] at hTwo
  exact (smul_add_lower_ne_C410 (320 * delta : k) q (A ^ 3)
    (gammaI2DeltaA3Rest410 gamma delta zeta eta theta A B U)
    (3 * A.natDegree) (mul_ne_zero (by norm_num) hray.1)
    (pow_ne_zero 3 hA) (by omega) (by rw [natDegree_pow]) hrest) hTwo

def GammaI2ZeroFaceCoreNonzeroSelector410
    (L : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      U ^ 2 - (8 : k) • (A * B ^ 2) ≠ 0) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceTieCoreRaysSelector410_coreZero_elimination
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (L : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2ZeroFaceTieCoreRaysSelector410 delta L A B U) :
    GammaI2ZeroFaceCoreNonzeroSelector410 L A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · right
    left
    refine ⟨htie.1, ?_⟩
    by_cases hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0
    · rcases htie.2 with hcorene | hhigh | hlow
      · exact (hcorene hcore).elim
      · exact (constantDiscriminantI2_gamma_fixedTie_coreZero_highRay_impossible
          gamma delta zeta eta theta q A B U hB hU hendpoint htie.1
            hcore hhigh hTwo).elim
      · exact (constantDiscriminantI2_gamma_fixedTie_coreZero_lowRay_impossible
          gamma delta zeta eta theta q A B U hB hU hendpoint htie.1
            hlow hTwo).elim
    · exact hcore
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionCoreNonzeroFan410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceCoreNonzeroSelector410
      (gammaI2DeltaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceCoreNonzeroSelector410
      (gammaI2ZetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceCoreNonzeroSelector410
        (gammaI2ThetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceCoreNonzeroSelector410
        (gammaI2BaseEnvelope410 B U) A B U)

theorem gammaI2FirstCompetitionTieCoreRaysFan410_coreZero_elimination
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2FirstCompetitionTieCoreRaysFan410
      delta zeta theta A B U) :
    GammaI2FirstCompetitionCoreNonzeroFan410 delta zeta theta A B U := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceTieCoreRaysSelector410_coreZero_elimination
        gamma delta zeta eta theta q A B U
          (gammaI2DeltaEnvelope410 A B U) hB hU hendpoint hTwo hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceTieCoreRaysSelector410_coreZero_elimination
        gamma delta zeta eta theta q A B U
          (gammaI2ZetaEnvelope410 A B U) hB hU hendpoint hTwo hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceTieCoreRaysSelector410_coreZero_elimination
        gamma delta zeta eta theta q A B U
          (gammaI2ThetaEnvelope410 A B U) hB hU hendpoint hTwo
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceTieCoreRaysSelector410_coreZero_elimination
        gamma delta zeta eta theta q A B U
          (gammaI2BaseEnvelope410 B U) hB hU hendpoint hTwo
            hbase.2.2.2⟩))

def FirstTieCoreZeroDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FirstTieCoreRaysGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionCoreNonzeroFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)

theorem firstTieCoreRaysGammaNewtonResidual410_coreZero_elimination
    (gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hold : FirstTieCoreRaysGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FirstTieCoreZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact gammaI2FirstCompetitionTieCoreRaysFan410_coreZero_elimination
    gamma delta zeta eta theta (2048 * k2) A B U
      hold.1.1.1.1.2 hold.1.1.1.1.1.2 hold.1.1.1.2 hTwoD hold.2

/-! ## Source-facing elimination -/

def GammaFirstTieCoreZeroDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FirstTieCoreZeroDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFirstTieCoreZeroDeletedNoncubic_residual
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
      GammaFirstTieCoreZeroDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaFirstTieCoreRaysNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      firstTieCoreRaysGammaNewtonResidual410_coreZero_elimination
        gamma delta zeta eta theta k2 A B C0 hTwo0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFirstTieCoreZeroDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaFirstTieCoreZeroDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFirstTieCoreZeroDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFirstTieCoreZeroDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaFirstTieCoreZeroDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaFirstTieCoreZeroDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFirstTieCoreZeroElimination410

end Max11DegreeRoutes
