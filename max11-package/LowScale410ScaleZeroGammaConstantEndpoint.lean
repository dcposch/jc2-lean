import LowScale410ScaleZeroGammaCoordinateFan

/-!
# Deleting the constant endpoint of the gamma coordinate fan

On the discriminant-zero face `A^2-4C0=0`, the zero-degree alternative
`deg A = deg B = 0` also forces `deg C0 = 0`.  The integrated terminal row
then vanishes, contradicting its prescribed nonzero constant.  We delete
this endpoint without restricting any later load.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaConstantEndpoint410

variable {k : Type*} [Field k] [CharZero k]

theorem gammaCoordinate_U_zero_constant_endpoint_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hA0 : A.natDegree = 0) (hB0 : B.natDegree = 0)
    (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hAC : A ^ 2 = (4 : k) • C0 := sub_eq_zero.mp hU
  have hdegree := congrArg Polynomial.natDegree hAC
  have hC0 : C0.natDegree = 0 := by
    rw [natDegree_pow, hA0, natDegree_smul _ (by norm_num)] at hdegree
    simpa using hdegree.symm
  exact betaCubicWall_balanced_constants_impossible
    alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hA0 hB0 hC0 hterminal hLower

def TerminalCoordinateGammaNewtonResidual410
    (delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  CoordinateGammaNewtonResidual410 delta zeta eta theta A B C0 ∧
    ¬ (A ^ 2 - (4 : k) • C0 = 0 ∧
      A.natDegree = 0 ∧ B.natDegree = 0)

theorem coordinateGammaNewtonResidual410_terminal_refinement
    (alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X])
    (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hold : CoordinateGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    TerminalCoordinateGammaNewtonResidual410
      delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  rintro ⟨hU, hA0, hB0⟩
  exact gammaCoordinate_U_zero_constant_endpoint_impossible
    alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0
      hU hA0 hB0 hterminal hLower

theorem terminalCoordinateGammaNewtonResidual410_zeroU_selector
    (alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X])
    (hterminal : terminal ≠ 0)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hold : TerminalCoordinateGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    A = 0 ∨ B = 0 ∨
      A.natDegree + 2 * B.natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
  have hsecond : GammaSecondCoreResidual410
      delta zeta eta theta A B C0 := hold.1.2
  rcases gammaSecondCoreResidual410_zeroU_refinement
      delta zeta eta theta A B C0 hU hsecond with
    hA | hB | hconstant | hcompetition
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact (hold.2 ⟨hU, hconstant.1, hconstant.2⟩).elim
  · exact Or.inr (Or.inr hcompetition)

/-! ## Constant, integrated, and normalized source wrappers -/

def GammaTerminalCoordinateNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      TerminalCoordinateGammaNewtonResidual410
        delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaTerminalCoordinateNoncubic_earlyLoad_residual
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
      GammaTerminalCoordinateNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaCoordinateNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hLower0 : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal := by
    simpa [hold.1] using hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      coordinateGammaNewtonResidual410_terminal_refinement
        alpha beta gamma delta epsilon zeta eta theta iota terminal
          A B C0 hterminal hLower0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaTerminalCoordinateNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaTerminalCoordinateNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaTerminalCoordinateNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaTerminalCoordinateNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaTerminalCoordinateNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaTerminalCoordinateNoncubic_earlyLoad_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaConstantEndpoint410

end Max11DegreeRoutes
