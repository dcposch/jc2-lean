import LowScale410ScaleZeroGammaPrincipalWallElimination

/-!
# First Newton face split for the delta-plus-later-load sibling

On `l = beta = gamma = 0`, all zeta/eta/theta terms in the second invariant
lie below the envelope of the three nonzero-delta faces `A^3`, `A*U`, and
`B^2`.  Hence the two fixed faces either tie or one enters that sharp delta
envelope, modulo the explicit `B = 0` and `U = 0` coordinate leaves.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaLaterFirstFace410

variable {k : Type*} [Field k] [CharZero k]

def deltaLaterI2Envelope410 (A B U : k[X]) : ℕ :=
  max (3 * A.natDegree)
    (max (A.natDegree + U.natDegree) (2 * B.natDegree))

def deltaLaterI2DeltaFaces410 (delta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 - (640 * delta : k) • (A * U) +
    (1280 * delta : k) • B ^ 2

def deltaLaterI2Tail410
    (zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (768 * zeta : k) • A ^ 2 + (2048 * theta : k) • A +
    (4096 * eta : k) • B - (1536 * zeta : k) • U

theorem gammaI2LoadRest410_zeroGamma_eq_deltaFaces_add_tail
    (delta zeta eta theta : k) (A B U : k[X]) :
    gammaI2LoadRest410 0 delta zeta eta theta A B U =
      deltaLaterI2DeltaFaces410 delta A B U +
        deltaLaterI2Tail410 zeta eta theta A B U := by
  simp only [gammaI2LoadRest410, deltaLaterI2DeltaFaces410,
    deltaLaterI2Tail410, zero_mul, zero_smul, sub_zero]
  module

theorem deltaLaterI2DeltaFaces410_natDegree_le
    (delta : k) (A B U : k[X]) :
    (deltaLaterI2DeltaFaces410 delta A B U).natDegree ≤
      deltaLaterI2Envelope410 A B U := by
  simp only [deltaLaterI2DeltaFaces410, deltaLaterI2Envelope410]
  compute_degree

theorem deltaLaterI2Tail410_natDegree_le
    (zeta eta theta : k) (A B U : k[X]) :
    (deltaLaterI2Tail410 zeta eta theta A B U).natDegree ≤
      deltaLaterI2Envelope410 A B U := by
  simp only [deltaLaterI2Tail410, deltaLaterI2Envelope410]
  compute_degree
  omega

theorem gammaI2LoadRest410_zeroGamma_natDegree_le_deltaLaterEnvelope
    (delta zeta eta theta : k) (A B U : k[X]) :
    (gammaI2LoadRest410 0 delta zeta eta theta A B U).natDegree ≤
      deltaLaterI2Envelope410 A B U := by
  rw [gammaI2LoadRest410_zeroGamma_eq_deltaFaces_add_tail]
  exact (natDegree_add_le _ _).trans (max_le
    (deltaLaterI2DeltaFaces410_natDegree_le delta A B U)
    (deltaLaterI2Tail410_natDegree_le zeta eta theta A B U))

def DeltaLaterI2FirstFacePacket410 (A B U : k[X]) : Prop :=
  B = 0 ∨ U = 0 ∨
    GammaI2ZeroFaceSelector410 (deltaLaterI2Envelope410 A B U) A B U

theorem constantDiscriminantI2_deltaLater_firstFace_packet
    (delta zeta eta theta q : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q) :
    DeltaLaterI2FirstFacePacket410 A B U := by
  by_cases hB : B = 0
  · exact Or.inl hB
  by_cases hU : U = 0
  · exact Or.inr (Or.inl hU)
  right
  right
  exact constantDiscriminantI2_gamma_zeroFace_selector
    0 delta zeta eta theta q A B U (deltaLaterI2Envelope410 A B U)
      hB hU
      (gammaI2LoadRest410_zeroGamma_natDegree_le_deltaLaterEnvelope
        delta zeta eta theta A B U) hTwo

theorem constantIntegral410_deltaLater_firstFace_packet
    (delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k2) :
    DeltaLaterI2FirstFacePacket410 A B
      (A ^ 2 - (4 : k) • C0) := by
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact constantDiscriminantI2_deltaLater_firstFace_packet
    delta zeta eta theta (2048 * k2) A B
      (A ^ 2 - (4 : k) • C0) hTwoD

def GammaClosedDeltaFirstFaceNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCorePrincipalWallDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DeltaLaterI2FirstFacePacket410 A B
        (A ^ 2 - (4 : k) • C0))

theorem constantIntegral410_gammaClosedDeltaFirstFaceNoncubic_residual
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
    l = 0 ∧ GammaClosedDeltaFirstFaceNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaFullCorePrincipalWallDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · exact Or.inl hgamma
  · right
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hTwo
    exact ⟨hdelta.1, hdelta.2.1, hdelta.2.2.1, hdelta.2.2.2,
      constantIntegral410_deltaLater_firstFace_packet
        delta zeta eta theta k2 A B C0 hTwo0⟩

theorem integrated410_gammaClosedDeltaFirstFaceNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaClosedDeltaFirstFaceNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaClosedDeltaFirstFaceNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaClosedDeltaFirstFaceNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaClosedDeltaFirstFaceNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaClosedDeltaFirstFaceNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end DeltaLaterFirstFace410

end Max11DegreeRoutes
