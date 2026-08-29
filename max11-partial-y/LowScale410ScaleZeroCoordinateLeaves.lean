import LowScale410ScaleZeroA4AB3HighUTerminal

/-!
# Deleting the positive-beta coordinate leaves

The fan-restricted positive-`B` packet has no coordinate-degenerate
survivors.  On `A=0`, the prior bound `b≤u` makes `B U^2` uniquely leading
in `I2` unless `U=0`; the latter corner is deleted by the unique `B^4`
face in `I1`.  On `U=0`, the two previous fan inequalities force `a=b>0`,
and the already-proved low-`U` leading-coefficient resultant applies.

Thus only the two nondegenerate `I2` tie walls remain.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section CoordinateLeaves410

variable {k : Type*} [Field k] [CharZero k]

def scaleZeroZeroATwoRest410
    (beta gamma delta zeta eta : k) (B U : k[X]) : k[X] :=
  (1280 * delta : k) • B ^ 2 - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B + (336 * beta : k) • U ^ 2 -
    (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_zeroA_eq_BU2_face_add_rest
    (beta gamma delta zeta eta theta : k) (B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 beta gamma delta zeta eta theta 0 B U =
      (480 : k) • (B * U ^ 2) +
        scaleZeroZeroATwoRest410 beta gamma delta zeta eta B U := by
  simp [discriminantInvariantTwoNumerator410, scaleZeroZeroATwoRest410]
  module

theorem scaleZeroZeroATwoRest410_natDegree_lt
    (beta gamma delta zeta eta : k) (B U : k[X])
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hBleU : B.natDegree ≤ U.natDegree) :
    (scaleZeroZeroATwoRest410 beta gamma delta zeta eta B U).natDegree <
      B.natDegree + 2 * U.natDegree := by
  simp only [scaleZeroZeroATwoRest410]
  compute_degree
  omega

theorem scaleZero_positiveB_zeroA_nonzeroU_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hAzero : A = 0) (hUne : A ^ 2 - (4 : k) • C0 ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hBleU : B.natDegree ≤ (A ^ 2 - (4 : k) • C0).natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hU : U ≠ 0 := by simpa only [U] using hUne
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by
      have hbound : B.natDegree ≤ U.natDegree := by
        simpa only [U] using hBleU
      omega
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hrest := scaleZeroZeroATwoRest410_natDegree_lt
    beta gamma delta zeta eta B U hBpos hUpos
      (by simpa only [U] using hBleU)
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  subst A
  rw [discriminantInvariantTwo410_zeroA_eq_BU2_face_add_rest] at hTwoD
  exact (smul_add_lower_ne_C410 (480 : k) (2048 * k2) (B * U ^ 2)
    (scaleZeroZeroATwoRest410 beta gamma delta zeta eta B U)
    (B.natDegree + 2 * U.natDegree) (by norm_num)
    (mul_ne_zero hB (pow_ne_zero 2 hU)) (by omega)
    (by rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]) hrest) hTwoD

/-- Both coordinate alternatives in the remaining-two classification are
empty once the earlier fan packet is retained. -/
theorem scaleZero_positiveBeta_nondegenerate_remainingTwo_classification
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hbeta : beta ≠ 0)
    (hfan : FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    RemainingTwoScaleZeroI2TriangleTie410
      A B (A ^ 2 - (4 : k) • C0) := by
  have hBpos : 0 < B.natDegree := hfan.1.2.2.2.2
  have hold := scaleZero_positiveBeta_remainingTwo_I2_triangle_classification
    alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hbeta hBpos hTwo hOne hLower
  rcases hold with hA | hU | htie
  · by_cases hUzero : A ^ 2 - (4 : k) • C0 = 0
    · have hA_lt : A.natDegree < B.natDegree := by
        rw [hA, natDegree_zero]
        exact hBpos
      have hU_lt : (A ^ 2 - (4 : k) • C0).natDegree < B.natDegree := by
        rw [hUzero, natDegree_zero]
        exact hBpos
      exact (scaleZero_positiveB_B4_open_chamber_impossible
        beta gamma delta zeta eta theta k1 A B C0 hBpos hA_lt hU_lt
          hOne).elim
    · have hBleU : B.natDegree ≤
          (A ^ 2 - (4 : k) • C0).natDegree := by
        have hwall := hfan.2.1
        rw [hA, natDegree_zero, zero_max] at hwall
        simpa only [hA] using hwall
      exact (scaleZero_positiveB_zeroA_nonzeroU_impossible
        beta gamma delta zeta eta theta k2 A B C0 hA hUzero hBpos
          hBleU hTwo).elim
  · have hBwall := hfan.2.1
    rw [hU, natDegree_zero, max_zero] at hBwall
    have hApos : 0 < A.natDegree := by omega
    have hA4wall := hfan.2.2
    have hfirst : 4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree := by
      rcases hA4wall with hfirst | hsecond | hthird
      · exact hfirst
      · rw [hU, natDegree_zero] at hsecond
        omega
      · rw [hU, natDegree_zero] at hthird
        omega
    have hTie : 4 * A.natDegree =
        A.natDegree + 3 * B.natDegree := by omega
    have hUlow : (A ^ 2 - (4 : k) • C0).natDegree < A.natDegree := by
      rw [hU, natDegree_zero]
      exact hApos
    exact (scaleZero_positiveBeta_A4AB3_tie_lowU_impossible
      beta gamma delta zeta eta theta k2 k1 A B C0 hbeta hBpos hTie
        hUlow hTwo hOne).elim
  · exact htie

/-! ## Source-facing nondegenerate two-tie packet -/

def NondegenerateTwoTiePositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    RemainingTwoScaleZeroI2TriangleTie410
      A B (A ^ 2 - (4 : k) • C0)

def NondegenerateTwoTiePositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      NondegenerateTwoTiePositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_nondegenerateTwoTiePositiveB_earlyLoad_residual
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
      NondegenerateTwoTiePositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_remainingTwoPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan, hcoordinate⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_nondegenerate_remainingTwo_classification
      alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hbeta hfan
    · simpa [hold.1] using hTwo
    · simpa [hold.1] using hOne
    · simpa [hold.1] using hLower
  · exact Or.inr hlater

theorem integrated410_nondegenerateTwoTiePositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      NondegenerateTwoTiePositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_nondegenerateTwoTiePositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_nondegenerateTwoTiePositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          NondegenerateTwoTiePositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_nondegenerateTwoTiePositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end CoordinateLeaves410

end Max11DegreeRoutes
