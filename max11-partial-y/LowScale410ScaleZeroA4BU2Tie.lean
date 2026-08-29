import LowScale410ScaleZeroCoordinateLeaves

/-!
# Eliminating the `A^4 = B U^2` beta tie

On this remaining nondegenerate tie,

`4a = b + 2u`, `a + 3b ≤ 4a`,

so `b≤a`.  If `b<a`, the monomial `U^3` is uniquely leading in `I1`.
If `b=a`, the chamber is the triple point `a=b`, `2u=3a`, already
excluded by the terminal row.  Hence this entire tie is empty.

The sole surviving nondegenerate beta wall is therefore parameterized by
`a≤b` and `2u=a+2b`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section A4BU2Tie410

variable {k : Type*} [Field k] [CharZero k]

theorem scaleZeroU3RestOne410_natDegree_lt_on_A4BU2_tie
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = B.natDegree + 2 * U.natDegree)
    (hAB3 : A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree)
    (hBltA : B.natDegree < A.natDegree) :
    (lWallFanRestOneU3_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        3 * U.natDegree := by
  simp only [lWallFanRestOneU3_410, lWallIntermediateRestOne410,
    mul_zero, neg_zero, zero_smul, zero_add, add_zero]
  compute_degree
  omega

theorem scaleZero_positiveBeta_A4BU2_strict_tie_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree)
    (hAB3 : A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree)
    (hBltA : B.natDegree < A.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTie' : 4 * A.natDegree = B.natDegree + 2 * U.natDegree := by
    simpa only [U] using hTie
  have hUpos : 0 < U.natDegree := by omega
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUpos
    omega
  have hrest := scaleZeroU3RestOne410_natDegree_lt_on_A4BU2_tie
    beta gamma delta zeta eta theta A B U hBpos
      hTie' hAB3 hBltA
  have hOneD : discriminantInvariantOneNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [discriminantInvariantOneNumerator410_eq_fanU3_add_rest] at hOneD
  exact (smul_add_lower_ne_C410 (-(40 : k)) (2048 * k1) (U ^ 3)
    (lWallFanRestOneU3_410 0 beta gamma delta zeta eta theta A B U)
    (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hU) (by omega)
    (by rw [natDegree_pow]) hrest) hOneD

/-- Both the strict chamber and its triple-point boundary are empty. -/
theorem scaleZero_positiveBeta_A4BU2_tie_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hbeta : beta ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hTie : 4 * A.natDegree = B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree)
    (hAB3 : A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hBleA : B.natDegree ≤ A.natDegree := by omega
  by_cases hBA : B.natDegree = A.natDegree
  · have hFirst : 4 * A.natDegree =
        A.natDegree + 3 * B.natDegree := by omega
    have hUtop : 2 * (A ^ 2 - (4 : k) • C0).natDegree =
        3 * A.natDegree := by omega
    exact scaleZero_positiveBeta_A4AB3_highU_terminal_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
        A B C0 hbeta hBpos hFirst hUtop hTwo hLower
  · have hBltA : B.natDegree < A.natDegree := by omega
    exact scaleZero_positiveBeta_A4BU2_strict_tie_impossible
      beta gamma delta zeta eta theta k1 A B C0 hBpos hTie hAB3
        hBltA hOne

def FinalAB3BU2Tie410 (A B U : k[X]) : Prop :=
  A.natDegree ≤ B.natDegree ∧
    2 * U.natDegree = A.natDegree + 2 * B.natDegree

theorem scaleZero_positiveBeta_final_AB3BU2_classification
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
    FinalAB3BU2Tie410 A B (A ^ 2 - (4 : k) • C0) := by
  have hBpos : 0 < B.natDegree := hfan.1.2.2.2.2
  have hold := scaleZero_positiveBeta_nondegenerate_remainingTwo_classification
    alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hbeta hfan hTwo hOne hLower
  rcases hold with hfirst | hfinal
  · exact (scaleZero_positiveBeta_A4BU2_tie_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hbeta hBpos hfirst.1 hfirst.2 hTwo hOne hLower).elim
  · simp only [FinalAB3BU2Tie410]
    omega

/-! ## Source-facing final beta tie packet -/

def FinalTiePositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    FinalAB3BU2Tie410 A B (A ^ 2 - (4 : k) • C0)

def FinalTiePositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      FinalTiePositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_finalTiePositiveB_earlyLoad_residual
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
      FinalTiePositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_nondegenerateTwoTiePositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan, hties⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_final_AB3BU2_classification
      alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hbeta hfan
    · simpa [hold.1] using hTwo
    · simpa [hold.1] using hOne
    · simpa [hold.1] using hLower
  · exact Or.inr hlater

theorem integrated410_finalTiePositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      FinalTiePositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_finalTiePositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_finalTiePositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          FinalTiePositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_finalTiePositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end A4BU2Tie410

end Max11DegreeRoutes
