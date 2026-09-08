import LowScale410ScaleZeroGammaConstantEndpoint

/-!
# Deletion of the `U=0, A=0` gamma coordinate face

On this doubly degenerate face one has `C0=0`.  The second conserved
polynomial is then exactly `-(5/32) B^4 + theta B`.  Its quartic term
excludes positive-degree `B`, while the nonzero terminal row excludes the
constant endpoint.  No later load is set to zero.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaZeroAFace410

variable {k : Type*} [Field k] [CharZero k]

theorem gammaCoordinate_U_zero_A_zero_impossible
    (alpha gamma delta epsilon zeta eta theta iota k1 terminal : k)
    (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0) (hA : A = 0)
    (hterminal : terminal ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hscaled : (4 : k) • C0 = 0 := by
    simpa [hA] using hU
  have hC0 : C0 = 0 :=
    (smul_eq_zero.mp hscaled).resolve_left (by norm_num)
  subst A
  subst C0
  by_cases hB0 : B.natDegree = 0
  · exact betaCubicWall_balanced_constants_impossible
      alpha 0 gamma delta epsilon zeta eta theta iota terminal
        0 B 0 rfl hB0 rfl hterminal hLower
  · have hBpos : 0 < B.natDegree := by omega
    have hBne : B ≠ 0 := by
      intro hzero
      subst B
      exact hB0 natDegree_zero
    have hform : (-(5 / 32 : k)) • B ^ 4 + theta • B = C k1 := by
      simpa [firstIntegralOnePolynomial410] using hOne
    have hrest : (theta • B).natDegree < 4 * B.natDegree := by
      compute_degree
      omega
    exact (smul_add_lower_ne_C410 (-(5 / 32 : k)) k1 (B ^ 4)
      (theta • B) (4 * B.natDegree) (by norm_num)
      (pow_ne_zero 4 hBne) (by omega) (by rw [natDegree_pow]) hrest) hform

def ZeroADeletedGammaNewtonResidual410
    (delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  TerminalCoordinateGammaNewtonResidual410 delta zeta eta theta A B C0 ∧
    ¬ (A ^ 2 - (4 : k) • C0 = 0 ∧ A = 0)

theorem terminalCoordinateGammaNewtonResidual410_zeroA_refinement
    (alpha gamma delta epsilon zeta eta theta iota k1 terminal : k)
    (A B C0 : k[X])
    (hterminal : terminal ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hold : TerminalCoordinateGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    ZeroADeletedGammaNewtonResidual410 delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  rintro ⟨hU, hA⟩
  exact gammaCoordinate_U_zero_A_zero_impossible
    alpha gamma delta epsilon zeta eta theta iota k1 terminal A B C0
      hU hA hterminal hOne hLower

theorem zeroADeletedGammaNewtonResidual410_zeroU_selector
    (alpha gamma delta epsilon zeta eta theta iota k1 terminal : k)
    (A B C0 : k[X])
    (hterminal : terminal ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hold : ZeroADeletedGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    B = 0 ∨
      A.natDegree + 2 * B.natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
  rcases terminalCoordinateGammaNewtonResidual410_zeroU_selector
      alpha 0 gamma delta epsilon zeta eta theta iota terminal A B C0
        hterminal hLower hU hold.1 with hA | hB | hcompetition
  · exact (hold.2 ⟨hU, hA⟩).elim
  · exact Or.inl hB
  · exact Or.inr hcompetition

/-! ## Constant, integrated, and normalized source wrappers -/

def GammaZeroADeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      ZeroADeletedGammaNewtonResidual410
        delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaZeroADeletedNoncubic_earlyLoad_residual
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
      GammaZeroADeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaTerminalCoordinateNoncubic_earlyLoad_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · have hOne0 : firstIntegralOnePolynomial410
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
      terminalCoordinateGammaNewtonResidual410_zeroA_refinement
        alpha gamma delta epsilon zeta eta theta iota k1 terminal
          A B C0 hterminal hOne0 hLower0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaZeroADeletedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaZeroADeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaZeroADeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaZeroADeletedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaZeroADeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaZeroADeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaZeroAFace410

end Max11DegreeRoutes
