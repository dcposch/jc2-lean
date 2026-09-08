import LowScale410ScaleZeroDeltaLaterCoordinates

/-!
# Deletion of `A = 0` on the delta-plus-later-load sibling

On `A = 0` the terminal row is the derivative of an explicit primitive.
Its forced degree one leaves the ray `deg U = 3 deg B`; there the `B*U^2`
face is uniquely dominant in the second invariant.  Thus all three
coordinate polynomials are nonzero and the remaining packet is exactly the
fixed-face tie or one of the two fixed faces entering the delta envelope.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaLaterAZero410

variable {k : Type*} [Field k] [CharZero k]

def deltaLaterAZeroTerminalPrimitive410
    (delta zeta theta : k) (B U : k[X]) : k[X] :=
  (1280 : k) • (B ^ 3 * U) - (3072 * zeta : k) • B ^ 2 +
    (320 * delta : k) • U ^ 2 - (2048 * theta : k) • U

theorem lWallTerminal410_deltaLater_A_zero_eq_derivative
    (delta zeta eta theta : k) (B U : k[X]) :
    lWallTerminalNumerator410 0 0 0 delta zeta eta theta 0 B U =
      derivative (deltaLaterAZeroTerminalPrimitive410
        delta zeta theta B U) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    deltaLaterAZeroTerminalPrimitive410, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_smul,
    Polynomial.derivative_C, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

def deltaLaterAZeroI2Rest410
    (delta zeta eta : k) (B U : k[X]) : k[X] :=
  (1280 * delta : k) • B ^ 2 + (4096 * eta : k) • B -
    (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_deltaLater_A_zero_decomposition
    (delta zeta eta theta : k) (B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 0 delta zeta eta theta 0 B U =
      (480 : k) • (B * U ^ 2) +
        deltaLaterAZeroI2Rest410 delta zeta eta B U := by
  simp [discriminantInvariantTwoNumerator410,
    deltaLaterAZeroI2Rest410] <;> module

theorem deltaLater_A_zero_discriminant_impossible
    (delta zeta eta theta k2 terminal : k) (B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta 0 B U = C k2)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta 0 B U = C terminal) : False := by
  have hDerivative : derivative
      (deltaLaterAZeroTerminalPrimitive410 delta zeta theta B U) =
        C terminal := by
    rw [← lWallTerminal410_deltaLater_A_zero_eq_derivative]
    exact hTerminal
  have hDegree :
      (deltaLaterAZeroTerminalPrimitive410
        delta zeta theta B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (deltaLaterAZeroTerminalPrimitive410 delta zeta theta B U)
      terminal hterminal hDerivative
  by_cases hB0 : B.natDegree = 0
  · by_cases hU0 : U.natDegree = 0
    · have hle : (deltaLaterAZeroTerminalPrimitive410
          delta zeta theta B U).natDegree ≤ 0 := by
        simp only [deltaLaterAZeroTerminalPrimitive410]
        compute_degree
        omega
      omega
    · have hUpos : 0 < U.natDegree := by omega
      let R : k[X] := (1280 : k) • (B ^ 3 * U) -
        (3072 * zeta : k) • B ^ 2 - (2048 * theta : k) • U
      have hform : deltaLaterAZeroTerminalPrimitive410 delta zeta theta B U =
          (320 * delta : k) • U ^ 2 + R := by
        dsimp only [R]
        simp only [deltaLaterAZeroTerminalPrimitive410]
        module
      have hR : R.natDegree < 2 * U.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      have hmain : ((320 * delta : k) • U ^ 2).natDegree =
          2 * U.natDegree := by
        rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta),
          natDegree_pow]
      have hR' : R.natDegree < ((320 * delta : k) • U ^ 2).natDegree := by
        rw [hmain]
        exact hR
      have hPdegree : (deltaLaterAZeroTerminalPrimitive410
          delta zeta theta B U).natDegree = 2 * U.natDegree := by
        rw [hform, natDegree_add_eq_left_of_natDegree_lt hR', hmain]
      omega
  · have hBpos : 0 < B.natDegree := by omega
    have hdegree : U.natDegree = 3 * B.natDegree := by
      rcases lt_trichotomy (3 * B.natDegree + U.natDegree)
          (2 * U.natDegree) with hlt | hequal | hgt
      · let R : k[X] := (1280 : k) • (B ^ 3 * U) -
          (3072 * zeta : k) • B ^ 2 - (2048 * theta : k) • U
        have hform : deltaLaterAZeroTerminalPrimitive410
            delta zeta theta B U = (320 * delta : k) • U ^ 2 + R := by
          dsimp only [R]
          simp only [deltaLaterAZeroTerminalPrimitive410]
          module
        have hR : R.natDegree < 2 * U.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        have hmain : ((320 * delta : k) • U ^ 2).natDegree =
            2 * U.natDegree := by
          rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta),
            natDegree_pow]
        have hR' : R.natDegree < ((320 * delta : k) • U ^ 2).natDegree := by
          rw [hmain]
          exact hR
        have hPdegree : (deltaLaterAZeroTerminalPrimitive410
            delta zeta theta B U).natDegree = 2 * U.natDegree := by
          rw [hform, natDegree_add_eq_left_of_natDegree_lt hR', hmain]
        omega
      · omega
      · let R : k[X] := (320 * delta : k) • U ^ 2 -
          (3072 * zeta : k) • B ^ 2 - (2048 * theta : k) • U
        have hform : deltaLaterAZeroTerminalPrimitive410
            delta zeta theta B U = (1280 : k) • (B ^ 3 * U) + R := by
          dsimp only [R]
          simp only [deltaLaterAZeroTerminalPrimitive410]
          module
        have hR : R.natDegree < 3 * B.natDegree + U.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        have hmain : ((1280 : k) • (B ^ 3 * U)).natDegree =
            3 * B.natDegree + U.natDegree := by
          rw [natDegree_smul _ (by norm_num),
            natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
        have hR' : R.natDegree < ((1280 : k) • (B ^ 3 * U)).natDegree := by
          rw [hmain]
          exact hR
        have hPdegree : (deltaLaterAZeroTerminalPrimitive410
            delta zeta theta B U).natDegree =
              3 * B.natDegree + U.natDegree := by
          rw [hform, natDegree_add_eq_left_of_natDegree_lt hR', hmain]
        omega
    rw [discriminantInvariantTwo410_deltaLater_A_zero_decomposition]
      at hTwo
    have hrest : (deltaLaterAZeroI2Rest410
        delta zeta eta B U).natDegree <
          B.natDegree + 2 * U.natDegree := by
      simp only [deltaLaterAZeroI2Rest410]
      compute_degree
      omega
    have hmain : (B * U ^ 2).natDegree =
        B.natDegree + 2 * U.natDegree := by
      rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
    exact (smul_add_lower_ne_C410 (480 : k) k2 (B * U ^ 2)
      (deltaLaterAZeroI2Rest410 delta zeta eta B U)
      (B.natDegree + 2 * U.natDegree) (by norm_num)
      (mul_ne_zero hB (pow_ne_zero 2 hU)) (by omega) hmain hrest) hTwo

theorem deltaLater_A_zero_original_impossible
    (alpha delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X]) (hA : A = 0) (hB : B ≠ 0)
    (hU : A ^ 2 - (4 : k) • C0 ≠ 0)
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
        A B C0) B C0 = C terminal) : False := by
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (2048 * k2) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B (A ^ 2 - (4 : k) • C0) =
        C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  subst A
  exact deltaLater_A_zero_discriminant_impossible
    delta zeta eta theta (2048 * k2) (8192 * terminal) B
      (0 ^ 2 - (4 : k) • C0) hdelta
      (mul_ne_zero (by norm_num) hterminal) hB (by simpa using hU)
      (by simpa using hTwoD) (by simpa using hTerminalD)

def DeltaLaterADeletedFaceSelector410 (A B U : k[X]) : Prop :=
  A.natDegree + 3 * B.natDegree = B.natDegree + 2 * U.natDegree ∨
    A.natDegree + 3 * B.natDegree ≤ deltaLaterI2Envelope410 A B U ∨
    B.natDegree + 2 * U.natDegree ≤ deltaLaterI2Envelope410 A B U

def DeltaLaterAllCoordinatesDeletedFirstFacePacket410
    (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧ DeltaLaterADeletedFaceSelector410 A B U

theorem deltaLater_coordinatesDeleted_A_zero_refinement
    (alpha delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X]) (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
        A B C0) B C0 = C terminal)
    (hold : DeltaLaterCoordinateDeletedFirstFacePacket410 A B
      (A ^ 2 - (4 : k) • C0)) :
    DeltaLaterAllCoordinatesDeletedFirstFacePacket410 A B
      (A ^ 2 - (4 : k) • C0) := by
  have hA : A ≠ 0 := by
    intro hAzero
    exact deltaLater_A_zero_original_impossible
      alpha delta epsilon zeta eta theta iota k2 terminal A B C0
        hAzero hold.1 hold.2.1 hdelta hterminal hTwo hLower
  refine ⟨hA, hold.1, hold.2.1, ?_⟩
  rcases hold.2.2 with hAzero | htie | hABlow | hBUlow
  · exact (hA hAzero).elim
  · exact Or.inl htie
  · exact Or.inr (Or.inl hABlow)
  · exact Or.inr (Or.inr hBUlow)

def GammaClosedDeltaAllCoordinatesDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCorePrincipalWallDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DeltaLaterAllCoordinatesDeletedFirstFacePacket410 A B
        (A ^ 2 - (4 : k) • C0))

theorem constantIntegral410_gammaClosedDeltaAllCoordinatesDeletedNoncubic_residual
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
      GammaClosedDeltaAllCoordinatesDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaClosedDeltaCoordinatesDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · exact Or.inl hgamma
  · right
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hTwo
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
          A B C0) B C0 = C terminal := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hLower
    exact ⟨hdelta.1, hdelta.2.1, hdelta.2.2.1, hdelta.2.2.2.1,
      deltaLater_coordinatesDeleted_A_zero_refinement
        alpha delta epsilon zeta eta theta iota k2 terminal A B C0
          hdelta.2.2.1 hterminal hTwo0 hLower0 hdelta.2.2.2.2⟩

theorem integrated410_gammaClosedDeltaAllCoordinatesDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaClosedDeltaAllCoordinatesDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaClosedDeltaAllCoordinatesDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaClosedDeltaAllCoordinatesDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaClosedDeltaAllCoordinatesDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaClosedDeltaAllCoordinatesDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end DeltaLaterAZero410

end Max11DegreeRoutes
