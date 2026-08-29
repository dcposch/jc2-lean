import LowScale410ScaleZeroGammaDescendedCoreTieElimination

/-!
# Scalar packet for the final full-core fixed-face tie

If the degree-`3 deg U` first-invariant principal coefficient is nonzero,
the three-face selector forces the high ray (the low ray is impossible).
On that ray, the two constant invariants force two explicit leading-scalar
equations.  Thus only a principal cancellation wall or this finite scalar
ray packet survives.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFullCoreTieScalarPacket410

variable {k : Type*} [Field k] [CharZero k]

def gammaTiePrincipalTopScalar410 (A B U : k[X]) : k :=
  960 * A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff -
    40 * U.leadingCoeff ^ 3

def gammaTieFixedI2TopScalar410 (A B U : k[X]) : k :=
  -(1280 * A.leadingCoeff * B.leadingCoeff ^ 3) +
    480 * B.leadingCoeff * U.leadingCoeff ^ 2

theorem gammaConstantCorePrincipal410_top_coeff_raw
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree) :
    (gammaConstantCorePrincipal410 A B U).coeff (3 * U.natDegree) =
      gammaTiePrincipalTopScalar410 A B U := by
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * U.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * U.natDegree := by
    rw [natDegree_pow]
  rw [gammaConstantCorePrincipal410, coeff_sub, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff (3 * U.natDegree) =
        (A.leadingCoeff * B.leadingCoeff ^ 2) * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul,
        leadingCoeff_mul, leadingCoeff_pow],
    show (U ^ 3).coeff (3 * U.natDegree) = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow]]
  simp only [smul_eq_mul, gammaTiePrincipalTopScalar410]
  ring

theorem gammaConstantCorePrincipal410_natDegree_eq_of_top_ne_zero
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (htop : gammaTiePrincipalTopScalar410 A B U ≠ 0) :
    (gammaConstantCorePrincipal410 A B U).natDegree =
      3 * U.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simp only [gammaConstantCorePrincipal410]
    compute_degree
    omega
  · rw [gammaConstantCorePrincipal410_top_coeff_raw A B U hA hB hU htie]
    exact htop

theorem gammaDescendedCoreLowRest410_natDegree_lt_threeU_of_fullCore
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hUpos : 0 < U.natDegree)
    (hcoreDegree : (gammaTieCore410 A B U).natDegree =
      2 * U.natDegree) :
    (gammaDescendedCoreLowRest410
      gamma delta zeta eta theta A B U).natDegree < 3 * U.natDegree := by
  have hlow := gammaConstantCoreLowRest410_natDegree_lt_threeU
    delta zeta eta theta A B U hA hB hU htie hUpos
  simp only [gammaDescendedCoreLowRest410]
  compute_degree
  omega

def gammaTieFixedI2Face410 (A B U : k[X]) : k[X] :=
  (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2)

theorem discriminantInvariantTwo410_eq_fixedFace_add_loadRest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A B U =
      gammaTieFixedI2Face410 A B U +
        gammaI2LoadRest410 gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest]
  rfl

theorem gammaTieFixedI2Face410_top_coeff
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree) :
    (gammaTieFixedI2Face410 A B U).coeff
        (A.natDegree + 3 * B.natDegree) =
      gammaTieFixedI2TopScalar410 A B U := by
  have hAB3deg : (A * B ^ 3).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hBU2deg : (B * U ^ 2).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
    omega
  rw [gammaTieFixedI2Face410, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 3).coeff (A.natDegree + 3 * B.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff (A.natDegree + 3 * B.natDegree) =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]]
  simp only [smul_eq_mul, gammaTieFixedI2TopScalar410]
  ring

theorem constantDiscriminants_gamma_fullCore_nonzeroPrincipal_scalarPacket
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcoreDegree : (gammaTieCore410 A B U).natDegree =
      2 * U.natDegree)
    (hprincipal : gammaTiePrincipalTopScalar410 A B U ≠ 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2) :
    4 * B.natDegree = 3 * U.natDegree ∧
      gammaTieFixedI2TopScalar410 A B U = 0 ∧
      gammaTiePrincipalTopScalar410 A B U -
        320 * B.leadingCoeff ^ 4 = 0 := by
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  have hPdeg := gammaConstantCorePrincipal410_natDegree_eq_of_top_ne_zero
    A B U hA hB hU htie hprincipal
  have hRdeg := gammaDescendedCoreLowRest410_natDegree_lt_threeU_of_fullCore
    gamma delta zeta eta theta A B U hA hB hU htie hUpos hcoreDegree
  have hOneThree := hOne
  rw [discriminantInvariantOne410_eq_descendedCore_threeFaces] at hOneThree
  rcases gammaTie_threeFace_exactRays410 delta q1 A B U
      (gammaConstantCorePrincipal410 A B U)
      (gammaDescendedCoreLowRest410 gamma delta zeta eta theta A B U)
      hA hB hUpos htie hPdeg hRdeg hOneThree with hhigh | hlow
  · refine ⟨hhigh, ?_, ?_⟩
    have hload : (gammaI2LoadRest410
        gamma delta zeta eta theta A B U).natDegree <
          A.natDegree + 3 * B.natDegree := by
      simp only [gammaI2LoadRest410]
      compute_degree
      omega
    have hTwoFixed := hTwo
    rw [discriminantInvariantTwo410_eq_fixedFace_add_loadRest] at hTwoFixed
    have hcoeffTwo := congrArg
      (fun P : k[X] => P.coeff (A.natDegree + 3 * B.natDegree)) hTwoFixed
    rw [coeff_add,
      gammaTieFixedI2Face410_top_coeff A B U hA hB hU htie,
      coeff_eq_zero_of_natDegree_lt hload,
      show (C q2 : k[X]).coeff (A.natDegree + 3 * B.natDegree) = 0 by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_C]
        omega, add_zero] at hcoeffTwo
    exact hcoeffTwo
    have hB4deg : (B ^ 4).natDegree = 3 * U.natDegree := by
      rw [natDegree_pow]
      omega
    have hDdeg : (A ^ 2 * B).natDegree < 3 * U.natDegree := by
      rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
      omega
    have hcoeffOne := congrArg
      (fun P : k[X] => P.coeff (3 * U.natDegree)) hOneThree
    rw [coeff_add, coeff_add, coeff_sub,
      gammaConstantCorePrincipal410_top_coeff_raw A B U hA hB hU htie,
      coeff_smul,
      show (B ^ 4).coeff (3 * U.natDegree) = B.leadingCoeff ^ 4 by
        rw [← hB4deg, coeff_natDegree, leadingCoeff_pow],
      coeff_smul, coeff_eq_zero_of_natDegree_lt hDdeg,
      coeff_eq_zero_of_natDegree_lt hRdeg,
      show (C q1 : k[X]).coeff (3 * U.natDegree) = 0 by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_C]
        omega] at hcoeffOne
    simp only [smul_eq_mul, mul_zero, neg_zero, zero_add, add_zero] at hcoeffOne
    exact hcoeffOne
  · exact (constantDiscriminantI2_gamma_fixedTie_coreZero_lowRay_impossible
      gamma delta zeta eta theta q2 A B U hB hU hendpoint htie hlow hTwo).elim

def GammaFullCoreTieScalarPacket410 (A B U : k[X]) : Prop :=
  gammaTiePrincipalTopScalar410 A B U = 0 ∨
    (4 * B.natDegree = 3 * U.natDegree ∧
      gammaTieFixedI2TopScalar410 A B U = 0 ∧
      gammaTiePrincipalTopScalar410 A B U -
        320 * B.leadingCoeff ^ 4 = 0)

def GammaI2ZeroFaceFullCoreScalarSelector410
    (L K : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      gammaTieCore410 A B U ≠ 0 ∧
      (∃ n : ℕ, A.natDegree = 2 * n ∧
        U.natDegree = B.natDegree + n) ∧
      GammaCoreFullTieDegreePacket410 K A B U ∧
      GammaFullCoreTieScalarPacket410 A B U) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceFullCoreSelector410_scalar_refinement
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X]) (L K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hold : GammaI2ZeroFaceFullCoreSelector410 L K A B U) :
    GammaI2ZeroFaceFullCoreScalarSelector410 L K A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · by_cases hAzero : A = 0
    · exact Or.inl hAzero
    right
    left
    refine ⟨htie.1, htie.2.1, htie.2.2.1, htie.2.2.2, ?_⟩
    by_cases hprincipal : gammaTiePrincipalTopScalar410 A B U = 0
    · exact Or.inl hprincipal
    · exact Or.inr
        (constantDiscriminants_gamma_fullCore_nonzeroPrincipal_scalarPacket
          gamma delta zeta eta theta q1 q2 A B U hAzero hB hU hendpoint
            htie.1 htie.2.2.2.1 hprincipal hOne hTwo)
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionFullCoreScalarFan410
    (delta zeta theta : k) (A B U : k[X]) (K : ℕ) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceFullCoreScalarSelector410
      (gammaI2DeltaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceFullCoreScalarSelector410
      (gammaI2ZetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceFullCoreScalarSelector410
        (gammaI2ThetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceFullCoreScalarSelector410
        (gammaI2BaseEnvelope410 B U) K A B U)

theorem gammaI2FirstCompetitionFullCoreFan410_scalar_refinement
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X]) (K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hold : GammaI2FirstCompetitionFullCoreFan410
      delta zeta theta A B U K) :
    GammaI2FirstCompetitionFullCoreScalarFan410 delta zeta theta A B U K := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceFullCoreSelector410_scalar_refinement
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2DeltaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceFullCoreSelector410_scalar_refinement
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2ZetaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceFullCoreSelector410_scalar_refinement
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2ThetaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceFullCoreSelector410_scalar_refinement
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2BaseEnvelope410 B U) K hB hU hendpoint hOne hTwo
            hbase.2.2.2⟩))

def FullCoreScalarRefinedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionFullCoreScalarFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)
      (max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

theorem descendedCoreDeletedGammaNewtonResidual410_scalar_refinement
    (gamma delta zeta eta theta k1 k2 : k) (A B C0 : k[X])
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hold : DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FullCoreScalarRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  let K : ℕ := max
    (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
    (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hfan := gammaI2FirstCompetitionFullCoreFan410_scalar_refinement
    gamma delta zeta eta theta (2048 * k1) (2048 * k2) A B U K
      hold.1.1.1.1.1.1.1.1.2 hold.1.1.1.1.1.1.1.1.1.2
      hold.1.1.1.1.1.1.1.2 hOneD hTwoD hold.2
  simpa only [U, K] using hfan

/-! ## Source-facing scalar packet -/

def GammaFullCoreScalarNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCoreScalarRefinedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFullCoreScalarNoncubic_residual
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
    l = 0 ∧ GammaFullCoreScalarNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaDescendedCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      descendedCoreDeletedGammaNewtonResidual410_scalar_refinement
        gamma delta zeta eta theta k1 k2 A B C0 hOne0 hTwo0
          hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFullCoreScalarNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaFullCoreScalarNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFullCoreScalarNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFullCoreScalarNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaFullCoreScalarNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaFullCoreScalarNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFullCoreTieScalarPacket410

end Max11DegreeRoutes
