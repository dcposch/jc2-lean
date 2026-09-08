import LowScale410ScaleZeroGammaHighBDeltaZeroStrata

/-!
# Elimination of the last high-`B` theta packet

The terminal tie fixes `(deg A, deg B, deg U) = (5,3,1)n`.  In the second
invariant, `A B^3` then has degree `14n`, while all remaining theta/base
terms have degree at most `5n`.  Hence the whole cone `2 deg U <= deg B`
is impossible.
-/

noncomputable section

set_option maxHeartbeats 3500000

open Polynomial

namespace Max11DegreeRoutes

section GammaHighBThetaElimination410

variable {k : Type*} [Field k] [CharZero k]

def gammaHighBThetaI2Rest410
    (gamma eta theta : k) (A B U : k[X]) : k[X] :=
  (2048 * theta : k) • A + (480 : k) • (B * U ^ 2) -
    (1536 * gamma : k) • (B * U) + (4096 * eta : k) • B

theorem discriminantInvariantTwo410_delta_zeta_zero_eq_AB3_add_thetaRest
    (gamma eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma 0 0 eta theta A B U =
      (-(1280 : k)) • (A * B ^ 3) +
        gammaHighBThetaI2Rest410 gamma eta theta A B U := by
  simp [discriminantInvariantTwoNumerator410, gammaHighBThetaI2Rest410]
  module

theorem gamma_highB_theta_packet_impossible
    (gamma eta theta q2 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (hpacket : GammaHighBThetaTerminalPacket410 theta A B U)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 eta theta A B U = C q2) : False := by
  rw [discriminantInvariantTwo410_delta_zeta_zero_eq_AB3_add_thetaRest]
    at hTwo
  have hmain : (A * B ^ 3).natDegree = 14 * U.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow,
      hpacket.1, hpacket.2.1]
    omega
  have hrest : (gammaHighBThetaI2Rest410
      gamma eta theta A B U).natDegree < 14 * U.natDegree := by
    simp only [gammaHighBThetaI2Rest410]
    compute_degree
    rw [hpacket.1, hpacket.2.1]
    omega
  exact (smul_add_lower_ne_C410 (-(1280 : k)) q2 (A * B ^ 3)
    (gammaHighBThetaI2Rest410 gamma eta theta A B U)
    (14 * U.natDegree) (by norm_num)
    (mul_ne_zero hA (pow_ne_zero 3 hB)) (by omega) hmain hrest) hTwo

def GammaThreeBroadPositiveCones410 (A B U : k[X]) : Prop :=
  3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree

def GammaHighBConeDeletedSelector410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      GammaThreeBroadPositiveCones410 A B U

def HighBConeDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaHighBConeDeletedSelector410 A B (A ^ 2 - (4 : k) • C0)

def HighBConeDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    HighBConeDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_highBConeDeletedNoncubic_residual
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
    l = 0 ∧ HighBConeDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_highBThetaOnlyNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hTwo0 : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2 := by
    simpa [hold.1, hold.2.1] using hTwo
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hdesc := hold.2.2.2.2.1
  have hsel := hold.2.2.2.2.2
  refine ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1,
    hdesc, hsel.1, hsel.2.1, hsel.2.2.1,
    hsel.2.2.2.1, hsel.2.2.2.2.1, ?_⟩
  simp only [GammaThreeBroadPositiveCones410]
  rcases hsel.2.2.2.2.2 with h1 | h2 | h3 | hhigh
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · have hthetaPacket := hhigh.2.2.2.2.2
    have hTwoT : discriminantInvariantTwoNumerator410
        0 0 gamma 0 0 eta theta A B U = C (2048 * k2) := by
      simpa only [hhigh.2.1, hhigh.2.2.1] using hTwoD
    exact (gamma_highB_theta_packet_impossible
      gamma eta theta (2048 * k2) A B U hsel.1 hsel.2.1
        hsel.2.2.1 hsel.2.2.2.2.1 hthetaPacket hTwoT).elim

theorem integrated410_highBConeDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ HighBConeDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_highBConeDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_highBConeDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        HighBConeDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_highBConeDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaHighBThetaElimination410

end Max11DegreeRoutes
