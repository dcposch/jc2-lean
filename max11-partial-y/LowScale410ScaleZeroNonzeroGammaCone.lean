import LowScale410ScaleZeroFinalAB3BU2Elimination

/-!
# The nonzero-gamma Newton packet with arbitrary later loads

After `l=beta=0`, set `U=A^2-4C0`.  The gamma faces of the two invariants
are exactly

`-(3/4) gamma (B U)`, `(3/32) gamma (U^2-8 A B^2)`.

This file separates them from the unrestricted `delta,zeta,eta,theta`
remainder and excludes both open chambers where a nonzero gamma face is the
unique positive-degree leader.  No later load is assumed to vanish.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section NonzeroGammaCone410

variable {k : Type*} [Field k] [CharZero k]

def gammaLoadTwoCorePolynomial410 (A B C0 : k[X]) : k[X] :=
  B * (A ^ 2 - (4 : k) • C0)

def gammaLoadOneCorePolynomial410 (A B C0 : k[X]) : k[X] :=
  (A ^ 2 - (4 : k) • C0) ^ 2 - (8 : k) • (A * B ^ 2)

def gammaLoadTwoPolynomial410 (gamma : k) (A B C0 : k[X]) : k[X] :=
  -(3 / 4 * gamma : k) • (A ^ 2 * B) +
    (3 * gamma : k) • (B * C0)

def gammaLoadOnePolynomial410 (gamma : k) (A B C0 : k[X]) : k[X] :=
  (3 / 32 * gamma : k) • A ^ 4 -
    (3 / 4 * gamma : k) • (A ^ 2 * C0) -
    (3 / 4 * gamma : k) • (A * B ^ 2) +
    (3 / 2 * gamma : k) • C0 ^ 2

def gammaLaterTwoRest410
    (delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  -(5 / 32 * delta : k) • A ^ 3 +
    (5 / 4 * delta : k) • (A * C0) +
    (5 / 8 * delta : k) • B ^ 2 -
    (3 / 8 * zeta : k) • A ^ 2 + (3 * zeta : k) • C0 +
    (2 * eta : k) • B + theta • A

def gammaLaterOneRest410
    (delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  -(15 / 32 * delta : k) • (A ^ 2 * B) +
    (5 / 4 * delta : k) • (B * C0) -
    (3 / 4 * zeta : k) • (A * B) -
    (1 / 2 * eta : k) • A ^ 2 + (2 * eta : k) • C0 + theta • B

theorem loadCorrectionTwo410_eq_gamma_add_later
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    loadCorrectionTwoPolynomial410 0 0 gamma delta zeta eta theta A B C0 =
      gammaLoadTwoPolynomial410 gamma A B C0 +
        gammaLaterTwoRest410 delta zeta eta theta A B C0 := by
  simp [loadCorrectionTwoPolynomial410, gammaLoadTwoPolynomial410,
    gammaLaterTwoRest410]
  module

theorem loadCorrectionOne410_eq_gamma_add_later
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    loadCorrectionOnePolynomial410 0 0 gamma delta zeta eta theta A B C0 =
      gammaLoadOnePolynomial410 gamma A B C0 +
        gammaLaterOneRest410 delta zeta eta theta A B C0 := by
  simp [loadCorrectionOnePolynomial410, gammaLoadOnePolynomial410,
    gammaLaterOneRest410]
  module

def NonzeroGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (gammaLoadTwoPolynomial410 gamma A B C0 = 0 ∨
      (gammaLoadTwoPolynomial410 gamma A B C0).natDegree = 0 ∨
      (gammaLoadTwoPolynomial410 gamma A B C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterTwoRest410 delta zeta eta theta A B C0).natDegree) ∧
    (gammaLoadOnePolynomial410 gamma A B C0 = 0 ∨
      (gammaLoadOnePolynomial410 gamma A B C0).natDegree = 0 ∨
      (gammaLoadOnePolynomial410 gamma A B C0).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

/-- Constant invariants forbid both unique-gamma chambers while keeping all
four later effective loads arbitrary. -/
theorem constantIntegrals410_nonzeroGamma_newton_residual
    (gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hgamma : gamma ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1) :
    NonzeroGammaNewtonResidual410 gamma delta zeta eta theta A B C0 := by
  constructor
  · by_cases hface : gammaLoadTwoPolynomial410 gamma A B C0 = 0
    · exact Or.inl hface
    right
    by_cases hdegree : (gammaLoadTwoPolynomial410 gamma A B C0).natDegree = 0
    · exact Or.inl hdegree
    right
    by_contra hle
    have hstrict :
        max
            (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0
              A B C0).natDegree
            (gammaLaterTwoRest410 delta zeta eta theta A B C0).natDegree <
          (gammaLoadTwoPolynomial410 gamma A B C0).natDegree := by
      omega
    have hrest :
        (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
            gammaLaterTwoRest410 delta zeta eta theta A B C0).natDegree <
          (gammaLoadTwoPolynomial410 gamma A B C0).natDegree := by
      exact (natDegree_add_le _ _).trans_lt (by omega)
    have heq :
        gammaLoadTwoPolynomial410 gamma A B C0 +
            (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
              gammaLaterTwoRest410 delta zeta eta theta A B C0) = C k2 := by
      rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
        loadCorrectionTwo410_eq_gamma_add_later] at hTwo
      simpa only [add_assoc, add_left_comm,
        add_comm] using hTwo
    exact (smul_add_lower_ne_C410 (1 : k) k2
      (gammaLoadTwoPolynomial410 gamma A B C0)
      (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
        gammaLaterTwoRest410 delta zeta eta theta A B C0)
      (gammaLoadTwoPolynomial410 gamma A B C0).natDegree
      (by norm_num) hface (by omega) rfl hrest) (by simpa using heq)
  · by_cases hface : gammaLoadOnePolynomial410 gamma A B C0 = 0
    · exact Or.inl hface
    right
    by_cases hdegree : (gammaLoadOnePolynomial410 gamma A B C0).natDegree = 0
    · exact Or.inl hdegree
    right
    by_contra hle
    have hstrict :
        max
            (firstIntegralOnePolynomial410 0 0 0 0 0 0 0
              A B C0).natDegree
            (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree <
          (gammaLoadOnePolynomial410 gamma A B C0).natDegree := by
      omega
    have hrest :
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
            gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree <
          (gammaLoadOnePolynomial410 gamma A B C0).natDegree := by
      exact (natDegree_add_le _ _).trans_lt (by omega)
    have heq :
        gammaLoadOnePolynomial410 gamma A B C0 +
            (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
              gammaLaterOneRest410 delta zeta eta theta A B C0) = C k1 := by
      rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
        loadCorrectionOne410_eq_gamma_add_later] at hOne
      simpa only [add_assoc, add_left_comm,
        add_comm] using hOne
    exact (smul_add_lower_ne_C410 (1 : k) k1
      (gammaLoadOnePolynomial410 gamma A B C0)
      (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
        gammaLaterOneRest410 delta zeta eta theta A B C0)
      (gammaLoadOnePolynomial410 gamma A B C0).natDegree
      (by norm_num) hface (by omega) rfl hrest) (by simpa using heq)

/-! ## Source-facing gamma packet -/

def GammaNewtonNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      NonzeroGammaNewtonResidual410 gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaNewtonNoncubic_earlyLoad_residual
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
      GammaNewtonNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_betaDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    refine ⟨hgamma.1, hgamma.2.1, hgamma.2.2, ?_⟩
    apply constantIntegrals410_nonzeroGamma_newton_residual
      gamma delta zeta eta theta k2 k1 A B C0 hgamma.2.1
    · simpa [hold.1, hgamma.1] using hTwo
    · simpa [hold.1, hgamma.1] using hOne
  · exact Or.inr hdelta

theorem integrated410_gammaNewtonNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaNewtonNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaNewtonNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaNewtonNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaNewtonNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaNewtonNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end NonzeroGammaCone410

end Max11DegreeRoutes
