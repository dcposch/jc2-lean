import LowScale410ScaleZeroDeltaLaterFirstFace

/-!
# Coordinate deletion for the delta-plus-later-load sibling

The `B = 0` face is already impossible for arbitrary effective loads.  On
`U = 0`, positive coordinate degrees force the nonzero-delta ray
`2 deg A = 3 deg B` and the scalar wall
`lc(B)^3 + delta lc(A)^2 = 0`; the terminal row deletes that ray.  The
degree-zero boundaries are deleted directly.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section DeltaLaterCoordinates410

variable {k : Type*} [Field k] [CharZero k]

theorem constantIntegralOne410_delta_U_zero_positive_degree_ray
    (delta zeta eta theta k1 : k) (A B : k[X])
    (hdelta : delta ≠ 0) (hApos : 0 < A.natDegree)
    (hBpos : 0 < B.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k1) :
    2 * A.natDegree = 3 * B.natDegree ∧
      B.leadingCoeff ^ 3 + delta * A.leadingCoeff ^ 2 = 0 := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hA2Bdeg : (A ^ 2 * B).natDegree =
      2 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
  have hB4deg : (B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
  have hspecial := hOne
  rw [firstIntegralOne410_discriminantZero_specialization] at hspecial
  let Rlow : k[X] := gammaUZeroLowerRestOne410 zeta theta A B
  have heq : (-(5 / 32 : k)) • B ^ 4 +
      ((-(5 / 32 * delta : k)) • (A ^ 2 * B) + Rlow) = C k1 := by
    simpa [Rlow, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hspecial
  have hdegrees : 2 * A.natDegree + B.natDegree =
      4 * B.natDegree := by
    rcases lt_trichotomy
        (2 * A.natDegree + B.natDegree) (4 * B.natDegree) with
      hlt | hequal | hgt
    · have hrest :
          ((-(5 / 32 * delta : k)) • (A ^ 2 * B) + Rlow).natDegree <
            4 * B.natDegree := by
        dsimp only [Rlow]
        simp only [gammaUZeroLowerRestOne410]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (-(5 / 32 : k)) k1 (B ^ 4)
        ((-(5 / 32 * delta : k)) • (A ^ 2 * B) + Rlow)
        (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB)
        (by omega) hB4deg hrest heq).elim
    · exact hequal
    · have hrest :
          ((-(5 / 32 : k)) • B ^ 4 + Rlow).natDegree <
            2 * A.natDegree + B.natDegree := by
        dsimp only [Rlow]
        simp only [gammaUZeroLowerRestOne410]
        compute_degree
        omega
      have heq' : (-(5 / 32 * delta : k)) • (A ^ 2 * B) +
          ((-(5 / 32 : k)) • B ^ 4 + Rlow) = C k1 := by
        simpa only [add_assoc, add_left_comm, add_comm] using heq
      exact (smul_add_lower_ne_C410 (-(5 / 32 * delta : k)) k1
        (A ^ 2 * B) ((-(5 / 32 : k)) • B ^ 4 + Rlow)
        (2 * A.natDegree + B.natDegree)
        (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
        (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hA2Bdeg hrest
        heq').elim
  have hRlow : Rlow.natDegree < 4 * B.natDegree := by
    dsimp only [Rlow]
    simp only [gammaUZeroLowerRestOne410]
    compute_degree
    omega
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (4 * B.natDegree)) heq
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (B ^ 4).coeff (4 * B.natDegree) = B.leadingCoeff ^ 4 by
      rw [← hB4deg, coeff_natDegree, leadingCoeff_pow],
    show (A ^ 2 * B).coeff (4 * B.natDegree) =
        A.leadingCoeff ^ 2 * B.leadingCoeff by
      rw [← hdegrees, ← hA2Bdeg, coeff_natDegree, leadingCoeff_mul,
        leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hRlow, add_zero,
    show (C k1 : k[X]).coeff (4 * B.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  refine ⟨by omega, ?_⟩
  apply (mul_left_cancel₀ hBlc)
  linear_combination (-32 / 5 : k) * hcoeff

theorem constantIntegralOne410_delta_U_zero_B_degree_zero_impossible
    (delta zeta eta theta k1 : k) (A B : k[X])
    (hdelta : delta ≠ 0) (hApos : 0 < A.natDegree)
    (hB0 : B.natDegree = 0) (hB : B ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k1) :
    False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hspecial := hOne
  rw [firstIntegralOne410_discriminantZero_specialization] at hspecial
  let R : k[X] := (-(5 / 32 : k)) • B ^ 4 +
    gammaUZeroLowerRestOne410 zeta theta A B
  have heq : (-(5 / 32 * delta : k)) • (A ^ 2 * B) + R = C k1 := by
    simpa [R, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hspecial
  have hrest : R.natDegree < 2 * A.natDegree := by
    dsimp only [R]
    simp only [gammaUZeroLowerRestOne410]
    compute_degree
    omega
  have hmain : (A ^ 2 * B).natDegree = 2 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow, hB0]
    omega
  exact (smul_add_lower_ne_C410 (-(5 / 32 * delta : k)) k1
    (A ^ 2 * B) R (2 * A.natDegree)
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
    (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hmain hrest) heq

theorem deltaLater_U_zero_original_impossible
    (alpha delta epsilon zeta eta theta iota k1 terminal : k)
    (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0) (hB : B ≠ 0)
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 0 delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 0 delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 0 delta epsilon zeta eta iota
        A B C0) B C0 = C terminal) : False := by
  have hAC : A ^ 2 = (4 : k) • C0 := sub_eq_zero.mp hU
  have hC0 : C0 = (1 / 4 : k) • A ^ 2 := by
    calc
      C0 = (1 / 4 : k) • ((4 : k) • C0) := by module
      _ = (1 / 4 : k) • A ^ 2 := by rw [← hAC]
  have hOne0 := hOne
  rw [hC0] at hOne0
  have hTerminalD : lWallTerminalNumerator410
      0 0 0 delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [hU] at hTerminalD
  by_cases hA0 : A.natDegree = 0
  · by_cases hB0 : B.natDegree = 0
    · have hdA : derivative A = 0 := derivative_eq_zero.mpr hA0
      have hdB : derivative B = 0 := derivative_eq_zero.mpr hB0
      have hzero : lWallTerminalNumerator410
          0 0 0 delta zeta eta theta A B 0 = 0 := by
        simp [lWallTerminalNumerator410, hdA, hdB]
      rw [hzero] at hTerminalD
      exact (mul_ne_zero (by norm_num) hterminal)
        (C_eq_zero.mp hTerminalD.symm)
    · exact gamma_U_zero_A_degree_zero_boundary_impossible
        0 delta zeta eta theta k1 A B hA0 (by omega) hOne0
  · have hApos : 0 < A.natDegree := by omega
    by_cases hB0 : B.natDegree = 0
    · exact constantIntegralOne410_delta_U_zero_B_degree_zero_impossible
        delta zeta eta theta k1 A B hdelta hApos hB0 hB hOne0
    · have hBpos : 0 < B.natDegree := by omega
      obtain ⟨hdegree, hscalar⟩ :=
        constantIntegralOne410_delta_U_zero_positive_degree_ray
          delta zeta eta theta k1 A B hdelta hApos hBpos hOne0
      exact gamma_U_zero_delta_ray_terminal_impossible
        0 delta zeta eta theta (8192 * terminal) A B hdelta hApos hBpos
          hdegree hscalar (mul_ne_zero (by norm_num) hterminal) hTerminalD

def DeltaLaterCoordinateDeletedFirstFacePacket410
    (A B U : k[X]) : Prop :=
  B ≠ 0 ∧ U ≠ 0 ∧
    GammaI2ZeroFaceSelector410 (deltaLaterI2Envelope410 A B U) A B U

theorem deltaLater_firstFace_coordinate_deletion
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
    (hold : DeltaLaterI2FirstFacePacket410 A B
      (A ^ 2 - (4 : k) • C0)) :
    DeltaLaterCoordinateDeletedFirstFacePacket410 A B
      (A ^ 2 - (4 : k) • C0) := by
  have hB : B ≠ 0 := by
    intro hBzero
    exact gamma_B_zero_original_impossible
      alpha 0 delta epsilon zeta eta theta iota k2 k1 terminal A B C0
        hBzero hterminal hTwo hOne hLower
  have hU : A ^ 2 - (4 : k) • C0 ≠ 0 := by
    intro hUzero
    exact deltaLater_U_zero_original_impossible
      alpha delta epsilon zeta eta theta iota k1 terminal A B C0
        hUzero hB hdelta hterminal hOne hLower
  refine ⟨hB, hU, ?_⟩
  rcases hold with hBzero | hUzero | hselector
  · exact (hB hBzero).elim
  · exact (hU hUzero).elim
  · exact hselector

def GammaClosedDeltaCoordinatesDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCorePrincipalWallDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DeltaLaterCoordinateDeletedFirstFacePacket410 A B
        (A ^ 2 - (4 : k) • C0))

theorem constantIntegral410_gammaClosedDeltaCoordinatesDeletedNoncubic_residual
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
      GammaClosedDeltaCoordinatesDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaClosedDeltaFirstFaceNoncubic_residual
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
      deltaLater_firstFace_coordinate_deletion
        alpha delta epsilon zeta eta theta iota k2 k1 terminal A B C0
          hdelta.2.2.1 hterminal hTwo0 hOne0 hLower0
            hdelta.2.2.2.2⟩

theorem integrated410_gammaClosedDeltaCoordinatesDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaClosedDeltaCoordinatesDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaClosedDeltaCoordinatesDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaClosedDeltaCoordinatesDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaClosedDeltaCoordinatesDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaClosedDeltaCoordinatesDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end DeltaLaterCoordinates410

end Max11DegreeRoutes
