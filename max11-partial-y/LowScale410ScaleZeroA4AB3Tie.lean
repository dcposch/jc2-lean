import LowScale410ScaleZeroPositiveBTriangleFan

/-!
# Refining the `A^4 = A B^3` scale-zero beta tie

On the first `I2` triangle wall one has `4a = a + 3b`, hence `a=b>0`.
If `u<a`, the two leading-face equations from `I2` and `I1` give
incompatible scalar relations between `beta lc(A)^3` and `lc(B)^3`.  If
`a<u` but `2u<3a`, the zero-load monomial `A B^2 U` is uniquely leading in
`I1`.  Consequently this whole wall reduces to the two exact subwalls
`u=a` and `2u=3a`, with every later load still arbitrary.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section A4AB3Tie410

variable {k : Type*} [Field k] [CharZero k]

def scaleZeroA4AB3RestTwo410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 - (336 * beta : k) • (A ^ 2 * U) +
    (768 * zeta : k) • A ^ 2 - (1344 * beta : k) • (A * B ^ 2) -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A +
    (1280 * delta : k) • B ^ 2 + (480 : k) • (B * U ^ 2) -
    (1536 * gamma : k) • (B * U) + (4096 * eta : k) • B +
    (336 * beta : k) • U ^ 2 - (1536 * zeta : k) • U

def scaleZeroA3BB4RestOne410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (960 : k) • (A * B ^ 2 * U) - (320 * delta : k) • (A ^ 2 * B) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (448 * beta : k) • B ^ 3 - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B -
    (40 : k) • U ^ 3 + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantTwo410_eq_A4AB3_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 beta gamma delta zeta eta theta A B U =
      (140 * beta : k) • A ^ 4 + (-(1280 : k)) • (A * B ^ 3) +
        scaleZeroA4AB3RestTwo410 beta gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantTwoNumerator410, scaleZeroA4AB3RestTwo410]
  module

theorem discriminantInvariantOne410_eq_A3BB4_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 beta gamma delta zeta eta theta A B U =
      (-(112 * beta : k)) • (A ^ 3 * B) +
        (-(320 : k)) • B ^ 4 +
        scaleZeroA3BB4RestOne410 beta gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410, scaleZeroA3BB4RestOne410]
  module

theorem scaleZeroA4AB3RestTwo410_natDegree_lt_of_lowU
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUlow : U.natDegree < A.natDegree) :
    (scaleZeroA4AB3RestTwo410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [scaleZeroA4AB3RestTwo410]
  compute_degree
  omega

theorem scaleZeroA3BB4RestOne410_natDegree_lt_of_lowU
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUlow : U.natDegree < A.natDegree) :
    (scaleZeroA3BB4RestOne410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [scaleZeroA3BB4RestOne410]
  compute_degree
  omega

/-- The low-discriminant part of the `A^4 = A B^3` wall is empty: its two
leading coefficient equations have nonzero resultant. -/
theorem scaleZero_positiveBeta_A4AB3_tie_lowU_impossible
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hUlow : (A ^ 2 - (4 : k) • C0).natDegree < A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hApos : 0 < A.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hrestTwo := scaleZeroA4AB3RestTwo410_natDegree_lt_of_lowU
    beta gamma delta zeta eta theta A B U hBpos hTie
      (by simpa only [U] using hUlow)
  have hrestOne := scaleZeroA3BB4RestOne410_natDegree_lt_of_lowU
    beta gamma delta zeta eta theta A B U hBpos hTie
      (by simpa only [U] using hUlow)
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
  rw [discriminantInvariantOne410_eq_A3BB4_face_add_rest] at hOneD
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
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A ^ 3 * B).coeff (4 * A.natDegree) =
        A.leadingCoeff ^ 3 * B.leadingCoeff by
      rw [← hA3Bdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B ^ 4).coeff (4 * A.natDegree) = B.leadingCoeff ^ 4 by
      rw [← hB4deg, coeff_natDegree, leadingCoeff_pow],
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
      -(112 * beta) * A.leadingCoeff ^ 3 - 320 * B.leadingCoeff ^ 3 = 0 := by
    apply (mul_left_cancel₀ hBlc)
    linear_combination hOneCoeff
  have hzero : (6720 : k) * B.leadingCoeff ^ 3 = 0 := by
    linear_combination -(4 : k) * hTwoCore - (5 : k) * hOneCore
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hBlc)) hzero

theorem scaleZeroAB2URestOne410_natDegree_lt_on_A4AB3_tie
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hAU : A.natDegree < U.natDegree)
    (hUtop : 2 * U.natDegree < 3 * A.natDegree) :
    (lWallFanRestOneAB2U_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        A.natDegree + 2 * B.natDegree + U.natDegree := by
  simp only [lWallFanRestOneAB2U_410, lWallIntermediateRestOne410,
    mul_zero, neg_zero, zero_smul, zero_add, add_zero]
  compute_degree
  omega

theorem scaleZero_positiveBeta_A4AB3_tie_middleU_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hAU : A.natDegree < (A ^ 2 - (4 : k) • C0).natDegree)
    (hUtop : 2 * (A ^ 2 - (4 : k) • C0).natDegree <
      3 * A.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hApos : 0 < A.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hU : U ≠ 0 := by
    intro hzero
    dsimp only [U] at hzero
    rw [hzero, natDegree_zero] at hAU
    omega
  have hrest := scaleZeroAB2URestOne410_natDegree_lt_on_A4AB3_tie
    beta gamma delta zeta eta theta A B U hBpos hTie
      (by simpa only [U] using hAU) (by simpa only [U] using hUtop)
  have hOneD : discriminantInvariantOneNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [discriminantInvariantOneNumerator410_eq_fanAB2U_add_rest] at hOneD
  exact (smul_add_lower_ne_C410 (960 : k) (2048 * k1) (A * B ^ 2 * U)
    (lWallFanRestOneAB2U_410 0 beta gamma delta zeta eta theta A B U)
    (A.natDegree + 2 * B.natDegree + U.natDegree) (by norm_num)
    (mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) hU) (by omega)
    (by
      rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
        natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]) hrest) hOneD

theorem scaleZero_positiveBeta_A4AB3_tie_refinement
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = A.natDegree + 3 * B.natDegree)
    (hBU2 : B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree ≤ 4 * A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) :
    (A ^ 2 - (4 : k) • C0).natDegree = A.natDegree ∨
      2 * (A ^ 2 - (4 : k) • C0).natDegree = 3 * A.natDegree := by
  by_cases hlow : (A ^ 2 - (4 : k) • C0).natDegree < A.natDegree
  · exact (scaleZero_positiveBeta_A4AB3_tie_lowU_impossible
      beta gamma delta zeta eta theta k2 k1 A B C0 hbeta hBpos hTie
        hlow hTwo hOne).elim
  by_cases heq : (A ^ 2 - (4 : k) • C0).natDegree = A.natDegree
  · exact Or.inl heq
  have hAU : A.natDegree < (A ^ 2 - (4 : k) • C0).natDegree := by omega
  have hUle : 2 * (A ^ 2 - (4 : k) • C0).natDegree ≤
      3 * A.natDegree := by omega
  by_cases htop : 2 * (A ^ 2 - (4 : k) • C0).natDegree =
      3 * A.natDegree
  · exact Or.inr htop
  have hUtop : 2 * (A ^ 2 - (4 : k) • C0).natDegree <
      3 * A.natDegree := by omega
  exact (scaleZero_positiveBeta_A4AB3_tie_middleU_impossible
    beta gamma delta zeta eta theta k1 A B C0 hBpos hTie hAU hUtop hOne).elim

def RefinedScaleZeroI2TriangleTie410 (A B U : k[X]) : Prop :=
  (4 * A.natDegree = A.natDegree + 3 * B.natDegree ∧
      B.natDegree + 2 * U.natDegree ≤ 4 * A.natDegree ∧
      (U.natDegree = A.natDegree ∨
        2 * U.natDegree = 3 * A.natDegree)) ∨
    (4 * A.natDegree = B.natDegree + 2 * U.natDegree ∧
      A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree) ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree)

theorem scaleZero_positiveBeta_refined_I2_triangle_classification
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) :
    A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      RefinedScaleZeroI2TriangleTie410 A B (A ^ 2 - (4 : k) • C0) := by
  have hold := scaleZero_positiveBeta_I2_triangle_classification
    beta gamma delta zeta eta theta k2 A B C0 hbeta hBpos hTwo
  rcases hold with hA | hU | htie
  · exact Or.inl hA
  · exact Or.inr (Or.inl hU)
  · right
    right
    rcases htie with hfirst | hsecond | hthird
    · left
      exact ⟨hfirst.1, hfirst.2,
        scaleZero_positiveBeta_A4AB3_tie_refinement
          beta gamma delta zeta eta theta k2 k1 A B C0 hbeta hBpos
            hfirst.1 hfirst.2 hTwo hOne⟩
    · exact Or.inr (Or.inl hsecond)
    · exact Or.inr (Or.inr hthird)

/-! ## Source-facing refined tie packet -/

def A4AB3RefinedPositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    (A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      RefinedScaleZeroI2TriangleTie410 A B (A ^ 2 - (4 : k) • C0))

def A4AB3RefinedPositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      A4AB3RefinedPositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_A4AB3RefinedPositiveB_earlyLoad_residual
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
      A4AB3RefinedPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_triangleFanPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan, htriangle⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_refined_I2_triangle_classification
      beta gamma delta zeta eta theta k2 k1 A B C0 hbeta
        hfan.1.2.2.2.2
    · simpa [hold.1] using hTwo
    · simpa [hold.1] using hOne
  · exact Or.inr hlater

theorem integrated410_A4AB3RefinedPositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      A4AB3RefinedPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_A4AB3RefinedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_A4AB3RefinedPositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          A4AB3RefinedPositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_A4AB3RefinedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end A4AB3Tie410

end Max11DegreeRoutes
