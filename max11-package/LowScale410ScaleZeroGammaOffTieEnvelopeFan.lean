import LowScale410ScaleZeroDeltaLaterElimination

/-!
# Exact off-tie envelope fan on the last gamma branch

The full-core fixed tie and the entire `gamma = 0, delta != 0` sibling are
already closed.  Here the two remaining fixed faces enter one of four load
envelopes.  Expanding each maximum gives an exact finite linear degree fan.
-/

noncomputable section

set_option maxHeartbeats 3000000

open Polynomial

namespace Max11DegreeRoutes

section GammaOffTieEnvelopeFan410

variable {k : Type*} [Field k] [CharZero k]

def GammaDeltaOffTieDegreeFan410 (A B U : k[X]) : Prop :=
  A = 0 ∨
    A.natDegree + 2 * B.natDegree ≤ U.natDegree ∨
    3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    A.natDegree + B.natDegree = 0 ∨
    U.natDegree = 0 ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree ∨
    B.natDegree + U.natDegree ≤ A.natDegree ∨
    2 * U.natDegree ≤ B.natDegree

def GammaZetaOffTieDegreeFan410 (A B U : k[X]) : Prop :=
  A = 0 ∨
    A.natDegree + 2 * B.natDegree ≤ U.natDegree ∨
    3 * B.natDegree ≤ A.natDegree ∨
    U.natDegree = 0 ∨
    B.natDegree + 2 * U.natDegree ≤ 2 * A.natDegree

def GammaThetaOffTieDegreeFan410 (A B U : k[X]) : Prop :=
  A = 0 ∨
    A.natDegree + 2 * B.natDegree ≤ U.natDegree ∨
    B.natDegree = 0 ∨
    U.natDegree = 0 ∨
    B.natDegree + 2 * U.natDegree ≤ A.natDegree

def GammaBaseOffTieDegreeFan410 (A B U : k[X]) : Prop :=
  A = 0 ∨ A.natDegree + 2 * B.natDegree ≤ U.natDegree ∨
    U.natDegree = 0

theorem gamma_delta_offTie_selector_exact_degree_fan
    (A B U : k[X])
    (hold : GammaI2ZeroFaceFullCoreTieDeletedSelector410
      (gammaI2DeltaEnvelope410 A B U) A B U) :
    GammaDeltaOffTieDegreeFan410 A B U := by
  rcases hold with hA | hAB | hBU
  · exact Or.inl hA
  · simp only [gammaI2DeltaEnvelope410] at hAB
    simp only [GammaDeltaOffTieDegreeFan410]
    omega
  · simp only [gammaI2DeltaEnvelope410] at hBU
    simp only [GammaDeltaOffTieDegreeFan410]
    omega

theorem gamma_zeta_offTie_selector_exact_degree_fan
    (A B U : k[X])
    (hold : GammaI2ZeroFaceFullCoreTieDeletedSelector410
      (gammaI2ZetaEnvelope410 A B U) A B U) :
    GammaZetaOffTieDegreeFan410 A B U := by
  rcases hold with hA | hAB | hBU
  · exact Or.inl hA
  · simp only [gammaI2ZetaEnvelope410] at hAB
    simp only [GammaZetaOffTieDegreeFan410]
    omega
  · simp only [gammaI2ZetaEnvelope410] at hBU
    simp only [GammaZetaOffTieDegreeFan410]
    omega

theorem gamma_theta_offTie_selector_exact_degree_fan
    (A B U : k[X])
    (hold : GammaI2ZeroFaceFullCoreTieDeletedSelector410
      (gammaI2ThetaEnvelope410 A B U) A B U) :
    GammaThetaOffTieDegreeFan410 A B U := by
  rcases hold with hA | hAB | hBU
  · exact Or.inl hA
  · simp only [gammaI2ThetaEnvelope410] at hAB
    simp only [GammaThetaOffTieDegreeFan410]
    omega
  · simp only [gammaI2ThetaEnvelope410] at hBU
    simp only [GammaThetaOffTieDegreeFan410]
    omega

theorem gamma_base_offTie_selector_exact_degree_fan
    (A B U : k[X])
    (hold : GammaI2ZeroFaceFullCoreTieDeletedSelector410
      (gammaI2BaseEnvelope410 B U) A B U) :
    GammaBaseOffTieDegreeFan410 A B U := by
  rcases hold with hA | hAB | hBU
  · exact Or.inl hA
  · simp only [gammaI2BaseEnvelope410] at hAB
    simp only [GammaBaseOffTieDegreeFan410]
    omega
  · simp only [gammaI2BaseEnvelope410] at hBU
    simp only [GammaBaseOffTieDegreeFan410]
    omega

def GammaI2FirstCompetitionExactOffTieFan410
    (delta zeta eta theta : k) (A B U : k[X]) : Prop :=
  (delta ≠ 0 ∧ GammaDeltaOffTieDegreeFan410 A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaZetaOffTieDegreeFan410 A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaThetaOffTieDegreeFan410 A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧ eta ≠ 0 ∧
      GammaBaseOffTieDegreeFan410 A B U)

theorem gamma_firstCompetition_tieDeleted_exactOffTie_refinement
    (delta zeta eta theta : k) (A B U : k[X])
    (hloads : delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)
    (hold : GammaI2FirstCompetitionFullCoreTieDeletedFan410
      delta zeta theta A B U) :
    GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gamma_delta_offTie_selector_exact_degree_fan A B U hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gamma_zeta_offTie_selector_exact_degree_fan A B U hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gamma_theta_offTie_selector_exact_degree_fan A B U htheta.2.2.2⟩))
  · right
    right
    right
    refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, ?_,
      gamma_base_offTie_selector_exact_degree_fan A B U hbase.2.2.2⟩
    rcases hloads with hdelta | hzeta | heta | htheta
    · exact (hdelta hbase.1).elim
    · exact (hzeta hbase.2.1).elim
    · exact heta
    · exact (htheta hbase.2.2.1).elim

def ExactOffTieFanGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionExactOffTieFan410 delta zeta eta theta A B
      (A ^ 2 - (4 : k) • C0)

theorem fullCorePrincipalDeleted_exactOffTie_refinement
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hloads : delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)
    (hold : FullCorePrincipalWallDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    ExactOffTieFanGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 :=
  ⟨hold.1,
    gamma_firstCompetition_tieDeleted_exactOffTie_refinement
      delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) hloads hold.2⟩

def ExactOffTieFanNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    ExactOffTieFanGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_exactOffTieFanNoncubic_residual
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
    l = 0 ∧ ExactOffTieFanNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_deltaLaterDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  exact ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1,
    fullCorePrincipalDeleted_exactOffTie_refinement
      gamma delta zeta eta theta A B C0 hold.2.2.2.1 hold.2.2.2.2⟩

theorem integrated410_exactOffTieFanNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ ExactOffTieFanNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_exactOffTieFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_exactOffTieFanNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        ExactOffTieFanNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_exactOffTieFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaOffTieEnvelopeFan410

end Max11DegreeRoutes
