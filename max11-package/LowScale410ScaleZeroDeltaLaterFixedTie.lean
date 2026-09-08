import LowScale410ScaleZeroDeltaLaterAZero

/-!
# Deletion of the fixed `AB^3 = BU^2` tie on the delta sibling

If the tied I2 coefficient is nonzero, the common degree enters the active
delta envelope.  If it vanishes, the I1 principal coefficient is nonzero;
the exact three-face selector leaves two rays, deleted respectively by the
terminal row and the nonzero-delta `A^3` face.  Hence the tie itself leaves
no new residual.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaLaterFixedTie410

variable {k : Type*} [Field k] [CharZero k]

theorem gammaTieFixedI2_zero_principal_ne_zero
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hfixed : gammaTieFixedI2TopScalar410 A B U = 0) :
    gammaTiePrincipalTopScalar410 A B U ≠ 0 := by
  intro hprincipal
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hfixed' :
      -(8 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 +
        3 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀
      (mul_ne_zero (by norm_num : (160 : k) ≠ 0) hBlc))
    simp only [gammaTieFixedI2TopScalar410] at hfixed
    linear_combination hfixed
  have hprincipal' :
      24 * A.leadingCoeff * B.leadingCoeff ^ 2 -
        U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀
      (mul_ne_zero (by norm_num : (40 : k) ≠ 0) hUlc))
    simp only [gammaTiePrincipalTopScalar410] at hprincipal
    linear_combination hprincipal
  have hzero : (64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 = 0 := by
    linear_combination 3 * hprincipal' + hfixed'
  exact (mul_ne_zero
    (mul_ne_zero (by norm_num) (leadingCoeff_ne_zero.mpr hA))
    (pow_ne_zero 2 hBlc)) hzero

theorem gammaTieFixedI2Face410_natDegree_eq_of_top_ne_zero
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (htop : gammaTieFixedI2TopScalar410 A B U ≠ 0) :
    (gammaTieFixedI2Face410 A B U).natDegree =
      A.natDegree + 3 * B.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simp only [gammaTieFixedI2Face410]
    compute_degree
    omega
  · rw [gammaTieFixedI2Face410_top_coeff A B U hA hB hU htie]
    exact htop

theorem constantDiscriminantI2_delta_tie_nonzeroTop_enters_envelope
    (delta zeta eta theta q : k) (A B U : k[X]) (L : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (htop : gammaTieFixedI2TopScalar410 A B U ≠ 0)
    (hrest : (gammaI2LoadRest410
      0 delta zeta eta theta A B U).natDegree ≤ L)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q) :
    A.natDegree + 3 * B.natDegree ≤ L := by
  by_contra hnot
  have hfaceDegree := gammaTieFixedI2Face410_natDegree_eq_of_top_ne_zero
    A B U hA hB hU htie htop
  have hface : gammaTieFixedI2Face410 A B U ≠ 0 := by
    intro hzero
    apply htop
    rw [← gammaTieFixedI2Face410_top_coeff A B U hA hB hU htie,
      hzero, coeff_zero]
  have hrestlt : (gammaI2LoadRest410
      0 delta zeta eta theta A B U).natDegree <
        A.natDegree + 3 * B.natDegree := by omega
  rw [discriminantInvariantTwo410_eq_fixedFace_add_loadRest] at hTwo
  exact (smul_add_lower_ne_C410 (1 : k) q
    (gammaTieFixedI2Face410 A B U)
    (gammaI2LoadRest410 0 delta zeta eta theta A B U)
    (A.natDegree + 3 * B.natDegree) (by norm_num) hface
    (by omega) hfaceDegree hrestlt) (by simpa using hTwo)

theorem deltaLater_fixedTie_zeroTop_impossible
    (delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hfixed : gammaTieFixedI2TopScalar410 A B U = 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B U = C terminal) : False := by
  by_cases hU0 : U.natDegree = 0
  · have hA0 : A.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    have hdA : derivative A = 0 := derivative_eq_zero.mpr hA0
    have hdB : derivative B = 0 := derivative_eq_zero.mpr hB0
    have hdU : derivative U = 0 := derivative_eq_zero.mpr hU0
    have hzero : lWallTerminalNumerator410
        0 0 0 delta zeta eta theta A B U = 0 := by
      simp [lWallTerminalNumerator410, hdA, hdB, hdU]
    rw [hzero] at hTerminal
    exact hterminal (C_eq_zero.mp hTerminal.symm)
  · have hUpos : 0 < U.natDegree := by omega
    have hprincipal := gammaTieFixedI2_zero_principal_ne_zero
      A B U hA hB hU hfixed
    have hPdegree := gammaConstantCorePrincipal410_natDegree_eq_of_top_ne_zero
      A B U hA hB hU htie hprincipal
    have hRdegree := gammaConstantCoreLowRest410_natDegree_lt_threeU
      delta zeta eta theta A B U hA hB hU htie hUpos
    have hdecomp := discriminantInvariantOne410_eq_descendedCore_threeFaces
      0 delta zeta eta theta A B U
    simp only [gammaDescendedCoreLowRest410, mul_zero, zero_smul,
      zero_add] at hdecomp
    rw [hdecomp] at hOne
    rcases gammaTie_threeFace_exactRays410 delta q1 A B U
        (gammaConstantCorePrincipal410 A B U)
        (gammaConstantCoreLowRest410 delta zeta eta theta A B U)
        hA hB hUpos htie hPdegree hRdegree hOne with hhigh | hlow
    · exact gamma_fullCore_highScalar_terminal_impossible
        0 delta zeta eta theta terminal A B U hA hB hU
          (by omega) htie hhigh hfixed hTerminal
    · exact constantDiscriminantI2_gamma_fixedTie_coreZero_lowRay_impossible
        0 delta zeta eta theta q2 A B U hB hU (by omega) htie hlow hTwo

theorem deltaLater_fixedTie_enters_envelope
    (delta zeta eta theta q2 q1 terminal : k) (A B U : k[X]) (L : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hrest : (gammaI2LoadRest410
      0 delta zeta eta theta A B U).natDegree ≤ L)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 0 delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B U = C terminal) :
    A.natDegree + 3 * B.natDegree ≤ L := by
  by_cases htop : gammaTieFixedI2TopScalar410 A B U = 0
  · exact (deltaLater_fixedTie_zeroTop_impossible
      delta zeta eta theta q2 q1 terminal A B U hA hB hU hdelta
        hterminal htie htop hTwo hOne hTerminal).elim
  · exact constantDiscriminantI2_delta_tie_nonzeroTop_enters_envelope
      delta zeta eta theta q2 A B U L hA hB hU htie htop hrest hTwo

def DeltaLaterTieDeletedFaceSelector410 (A B U : k[X]) : Prop :=
  A.natDegree + 3 * B.natDegree ≤ deltaLaterI2Envelope410 A B U ∨
    B.natDegree + 2 * U.natDegree ≤ deltaLaterI2Envelope410 A B U

def DeltaLaterFixedTieDeletedPacket410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧ DeltaLaterTieDeletedFaceSelector410 A B U

theorem deltaLater_allCoordinatesDeleted_fixedTie_refinement
    (alpha delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
        A B C0) B C0 = C terminal)
    (hold : DeltaLaterAllCoordinatesDeletedFirstFacePacket410 A B
      (A ^ 2 - (4 : k) • C0)) :
    DeltaLaterFixedTieDeletedPacket410 A B
      (A ^ 2 - (4 : k) • C0) := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 0 delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 0 0 delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B U = C (8192 * terminal) := by
    dsimp only [U]
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  refine ⟨hold.1, hold.2.1, hold.2.2.1, ?_⟩
  rcases hold.2.2.2 with htie | hABlow | hBUlow
  · exact Or.inl (deltaLater_fixedTie_enters_envelope
      delta zeta eta theta (2048 * k2) (2048 * k1) (8192 * terminal)
        A B U (deltaLaterI2Envelope410 A B U) hold.1 hold.2.1
        hold.2.2.1 hdelta (mul_ne_zero (by norm_num) hterminal) htie
        (gammaI2LoadRest410_zeroGamma_natDegree_le_deltaLaterEnvelope
          delta zeta eta theta A B U) hTwoD hOneD hTerminalD)
  · exact Or.inl hABlow
  · exact Or.inr hBUlow

def GammaClosedDeltaFixedTieDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCorePrincipalWallDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DeltaLaterFixedTieDeletedPacket410 A B
        (A ^ 2 - (4 : k) • C0))

theorem constantIntegral410_gammaClosedDeltaFixedTieDeletedNoncubic_residual
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
    l = 0 ∧ GammaClosedDeltaFixedTieDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaClosedDeltaAllCoordinatesDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · exact Or.inl hgamma
  · right
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hTwo
    have hOne0 : firstIntegralOnePolynomial410
        0 0 0 delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hOne
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
          A B C0) B C0 = C terminal := by
      simpa [hold.1, hdelta.1, hdelta.2.1] using hLower
    exact ⟨hdelta.1, hdelta.2.1, hdelta.2.2.1, hdelta.2.2.2.1,
      deltaLater_allCoordinatesDeleted_fixedTie_refinement
        alpha delta epsilon zeta eta theta iota k2 k1 terminal A B C0
          hdelta.2.2.1 hterminal hTwo0 hOne0 hLower0
            hdelta.2.2.2.2⟩

theorem integrated410_gammaClosedDeltaFixedTieDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaClosedDeltaFixedTieDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaClosedDeltaFixedTieDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaClosedDeltaFixedTieDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaClosedDeltaFixedTieDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaClosedDeltaFixedTieDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end DeltaLaterFixedTie410

end Max11DegreeRoutes
