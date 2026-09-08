import LowScale410ScaleZeroGammaHighBDeltaA4RaysElimination

/-!
# Deletion of the last nonzero-`delta` high-`B` ray

On `2 deg U <= deg B` and `deg A + deg U = 2 deg B`, the face
`delta A^4` is again uniquely dominant in the terminal fiber primitive.
Thus the high-`B` residual is entirely contained in `delta = 0`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaHighBCommonDeltaElimination410

variable {k : Type*} [Field k] [CharZero k]

theorem gamma_highB_delta_common_A4_ray_impossible
    (gamma delta zeta eta theta q2 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 2 * U.natDegree ≤ B.natDegree)
    (hray : A.natDegree + U.natDegree = 2 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal) : False := by
  have hDerivative : derivative
      (gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B U) =
        C terminal := by
    rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
      gamma delta zeta eta theta q2 A B U hTwo]
    exact hTerminal
  have hDegree : (gammaLaterFiberPrimitive410
      gamma delta zeta theta q2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B U)
      terminal hterminal hDerivative
  rw [gammaLaterFiberPrimitive410_eq_deltaA4_add_highBRest] at hDegree
  have hrest : (gammaHighBDeltaA4FiberRest410
      gamma delta zeta theta q2 A B U).natDegree < 4 * A.natDegree := by
    simp only [gammaHighBDeltaA4FiberRest410]
    compute_degree
    omega
  have hmain : ((560 * delta : k) • A ^ 4).natDegree =
      4 * A.natDegree := by
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
  rw [natDegree_add_eq_left_of_natDegree_lt (by
    rw [hmain]
    exact hrest), hmain] at hDegree
  omega

def GammaHighBDeltaZeroRay410
    (delta : k) (A B U : k[X]) : Prop :=
  delta = 0 ∧ A.natDegree + U.natDegree = 2 * B.natDegree

def GammaHighBDeltaZeroPositiveCones410
    (delta : k) (A B U : k[X]) : Prop :=
  3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree ∨
    (2 * U.natDegree ≤ B.natDegree ∧
      GammaHighBDeltaZeroRay410 delta A B U)

def GammaHighBDeltaZeroSelector410
    (delta : k) (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      GammaHighBDeltaZeroPositiveCones410 delta A B U

def HighBDeltaZeroGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaHighBDeltaZeroSelector410 delta A B (A ^ 2 - (4 : k) • C0)

def HighBDeltaZeroNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    HighBDeltaZeroGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_highBDeltaZeroNoncubic_residual
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
    l = 0 ∧ HighBDeltaZeroNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_highBDeltaA4ReducedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hTwo0 : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2 := by
    simpa [hold.1, hold.2.1] using hTwo
  have hLower0 : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal := by
    simpa [hold.1, hold.2.1] using hLower
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C (8192 * terminal) := by
    dsimp only [U]
    rw [← lowerRow410_discriminantTerminalNumerator, hLower0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hdesc := hold.2.2.2.2.1
  have hsel := hold.2.2.2.2.2
  refine ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1,
    hdesc, hsel.1, hsel.2.1, hsel.2.2.1,
    hsel.2.2.2.1, hsel.2.2.2.2.1, ?_⟩
  simp only [GammaHighBDeltaZeroPositiveCones410]
  rcases hsel.2.2.2.2.2 with h1 | h2 | h3 | hhigh
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · right
    right
    right
    refine ⟨hhigh.1, ?_⟩
    rcases hhigh.2 with hdelta0 | hdeltane
    · exact hdelta0
    · exact (gamma_highB_delta_common_A4_ray_impossible
        gamma delta zeta eta theta (2048 * k2) (8192 * terminal)
          A B U hdeltane.1 (mul_ne_zero (by norm_num) hterminal)
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 hhigh.1 hdeltane.2 hTwoD hTerminalD).elim

theorem integrated410_highBDeltaZeroNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ HighBDeltaZeroNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_highBDeltaZeroNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_highBDeltaZeroNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        HighBDeltaZeroNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_highBDeltaZeroNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaHighBCommonDeltaElimination410

end Max11DegreeRoutes
