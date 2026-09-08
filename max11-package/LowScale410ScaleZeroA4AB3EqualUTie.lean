import LowScale410ScaleZeroA4AB3Tie

/-!
# The equal-`U` component of the `A^4 = A B^3` beta tie

On `4a = a+3b` and `u=a`, the top `I2` face contains `beta A^4` and
`A B^3`, while the top `I1` face contains `beta A^3B`, `B^4`, and
`A B^2 U`.  Eliminating beta from their leading coefficient equations gives
the exact scalar wall

`5 lc(A) lc(U) = 7 lc(B)^2`.

No later load reaches these faces.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section A4AB3EqualUTie410

variable {k : Type*} [Field k] [CharZero k]

def scaleZeroA3BB4AB2URestOne410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(320 * delta : k) • (A ^ 2 * B) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (448 * beta : k) • B ^ 3 - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B - (40 : k) • U ^ 3 +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_eq_A3BB4AB2U_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 beta gamma delta zeta eta theta A B U =
      (-(112 * beta : k)) • (A ^ 3 * B) +
        (-(320 : k)) • B ^ 4 + (960 : k) • (A * B ^ 2 * U) +
        scaleZeroA3BB4AB2URestOne410
          beta gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410,
    scaleZeroA3BB4AB2URestOne410]
  module

theorem scaleZeroA4AB3RestTwo410_natDegree_lt_of_equalU
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUeq : U.natDegree = A.natDegree) :
    (scaleZeroA4AB3RestTwo410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [scaleZeroA4AB3RestTwo410]
  compute_degree
  omega

theorem scaleZeroA3BB4AB2URestOne410_natDegree_lt_of_equalU
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUeq : U.natDegree = A.natDegree) :
    (scaleZeroA3BB4AB2URestOne410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [scaleZeroA3BB4AB2URestOne410]
  compute_degree
  omega

/-- The exact leading-coefficient wall on the equal-`U` component. -/
theorem scaleZero_positiveBeta_A4AB3_equalU_scalar_wall
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUeq : (A ^ 2 - (4 : k) • C0).natDegree = A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) :
    (5 : k) * A.leadingCoeff *
        (A ^ 2 - (4 : k) • C0).leadingCoeff =
      7 * B.leadingCoeff ^ 2 := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hUeq' : U.natDegree = A.natDegree := by
    simpa only [U] using hUeq
  have hApos : 0 < A.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hUpos : 0 < U.natDegree := by omega
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUpos
    omega
  have hrestTwo := scaleZeroA4AB3RestTwo410_natDegree_lt_of_equalU
    beta gamma delta zeta eta theta A B U hBpos hTie
      hUeq'
  have hrestOne :=
    scaleZeroA3BB4AB2URestOne410_natDegree_lt_of_equalU
      beta gamma delta zeta eta theta A B U hBpos hTie
        hUeq'
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [discriminantInvariantTwo410_eq_A4AB3_face_add_rest] at hTwoD
  rw [discriminantInvariantOne410_eq_A3BB4AB2U_face_add_rest] at hOneD
  have hA4deg : (A ^ 4).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow]
  have hAB3deg : (A * B ^ 3).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
    omega
  have hA3Bdeg : (A ^ 3 * B).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hA) hB, natDegree_pow]
    omega
  have hB4deg : (B ^ 4).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 4 * A.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hTwoCoeff := congrArg
    (fun P : k[X] => P.coeff (4 * A.natDegree)) hTwoD
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A ^ 4).coeff (4 * A.natDegree) = A.leadingCoeff ^ 4 by
      rw [← hA4deg, coeff_natDegree, leadingCoeff_pow],
    show (A * B ^ 3).coeff (4 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hrestTwo, add_zero,
    show (C (2048 * k2) : k[X]).coeff (4 * A.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg
    (fun P : k[X] => P.coeff (4 * A.natDegree)) hOneD
  rw [coeff_add, coeff_add, coeff_add, coeff_smul, coeff_smul, coeff_smul,
    show (A ^ 3 * B).coeff (4 * A.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff by
      rw [← hA3Bdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B ^ 4).coeff (4 * A.natDegree) = B.leadingCoeff ^ 4 by
      rw [← hB4deg, coeff_natDegree, leadingCoeff_pow],
    show (A * B ^ 2 * U).coeff (4 * A.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hrestOne, add_zero,
    show (C (2048 * k1) : k[X]).coeff (4 * A.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hTwoCore :
      140 * beta * A.leadingCoeff ^ 3 - 1280 * B.leadingCoeff ^ 3 = 0 := by
    apply (mul_left_cancel₀ hAlc)
    linear_combination hTwoCoeff
  have hOneCore :
      -(112 * beta) * A.leadingCoeff ^ 3 - 320 * B.leadingCoeff ^ 3 +
        960 * A.leadingCoeff * B.leadingCoeff * U.leadingCoeff = 0 := by
    apply (mul_left_cancel₀ hBlc)
    linear_combination hOneCoeff
  change 5 * A.leadingCoeff * U.leadingCoeff = 7 * B.leadingCoeff ^ 2
  apply (mul_left_cancel₀
    (mul_ne_zero (by norm_num : (960 : k) ≠ 0) hBlc))
  linear_combination (5 : k) * hOneCore + (4 : k) * hTwoCore

def EqualUScalarRefinedScaleZeroI2TriangleTie410
    (A B U : k[X]) : Prop :=
  (4 * A.natDegree = A.natDegree + 3 * B.natDegree ∧
      B.natDegree + 2 * U.natDegree ≤ 4 * A.natDegree ∧
      ((U.natDegree = A.natDegree ∧
          (5 : k) * A.leadingCoeff * U.leadingCoeff =
            7 * B.leadingCoeff ^ 2) ∨
        2 * U.natDegree = 3 * A.natDegree)) ∨
    (4 * A.natDegree = B.natDegree + 2 * U.natDegree ∧
      A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree) ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree)

theorem scaleZero_positiveBeta_equalUScalar_I2_triangle_classification
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) :
    A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      EqualUScalarRefinedScaleZeroI2TriangleTie410
        A B (A ^ 2 - (4 : k) • C0) := by
  have hold := scaleZero_positiveBeta_refined_I2_triangle_classification
    beta gamma delta zeta eta theta k2 k1 A B C0 hbeta hBpos hTwo hOne
  rcases hold with hA | hU | htie
  · exact Or.inl hA
  · exact Or.inr (Or.inl hU)
  · right
    right
    rcases htie with hfirst | hsecond | hthird
    · left
      refine ⟨hfirst.1, hfirst.2.1, ?_⟩
      rcases hfirst.2.2 with heq | htop
      · left
        exact ⟨heq, scaleZero_positiveBeta_A4AB3_equalU_scalar_wall
          beta gamma delta zeta eta theta k2 k1 A B C0 hbeta hBpos
            hfirst.1 heq hTwo hOne⟩
      · exact Or.inr htop
    · exact Or.inr (Or.inl hsecond)
    · exact Or.inr (Or.inr hthird)

/-! ## Source-facing equal-`U` scalar packet -/

def EqualUScalarPositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    (A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      EqualUScalarRefinedScaleZeroI2TriangleTie410
        A B (A ^ 2 - (4 : k) • C0))

def EqualUScalarPositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      EqualUScalarPositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_equalUScalarPositiveB_earlyLoad_residual
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
      EqualUScalarPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_A4AB3RefinedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan, htriangle⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_equalUScalar_I2_triangle_classification
      beta gamma delta zeta eta theta k2 k1 A B C0 hbeta
        hfan.1.2.2.2.2
    · simpa [hold.1] using hTwo
    · simpa [hold.1] using hOne
  · exact Or.inr hlater

theorem integrated410_equalUScalarPositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      EqualUScalarPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_equalUScalarPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_equalUScalarPositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          EqualUScalarPositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_equalUScalarPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end A4AB3EqualUTie410

end Max11DegreeRoutes
