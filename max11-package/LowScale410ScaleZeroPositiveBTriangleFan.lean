import LowScale410ScaleZeroPositiveBFan

/-!
# The three-face scale-zero `I2` fan

On the positive-`B` beta residual, every monomial of the second discriminant
invariant lies under one of the three exposed weights

`4 deg A`, `deg A + 3 deg B`, `deg B + 2 deg U`.

The constant invariant forbids a strict unique maximum at each vertex.  Away
from the honest coordinate degeneracies `A = 0` and `U = 0`, the residual is
therefore confined to one of the three pairwise tie walls.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section PositiveBTriangleFan410

variable {k : Type*} [Field k] [CharZero k]

theorem scaleZeroAB3RestTwo410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hA4 : 4 * A.natDegree < A.natDegree + 3 * B.natDegree)
    (hBU2 : B.natDegree + 2 * U.natDegree <
      A.natDegree + 3 * B.natDegree) :
    (lWallFanRestTwoAB3_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        A.natDegree + 3 * B.natDegree := by
  simp only [lWallFanRestTwoAB3_410, lWallLowURestTwo410, mul_zero,
    neg_zero, zero_smul, zero_add, add_zero]
  compute_degree
  omega

theorem scaleZero_AB3_open_chamber_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hA : A ≠ 0) (hBpos : 0 < B.natDegree)
    (hA4 : 4 * A.natDegree < A.natDegree + 3 * B.natDegree)
    (hBU2 : B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree <
        A.natDegree + 3 * B.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hrest : (lWallFanRestTwoAB3_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        A.natDegree + 3 * B.natDegree := by
    apply scaleZeroAB3RestTwo410_natDegree_lt
    · exact hBpos
    · exact hA4
    · simpa only [U] using hBU2
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have heq : -(1280 : k) • (A * B ^ 3) +
      lWallFanRestTwoAB3_410
        0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    rw [← discriminantInvariantTwoNumerator410_eq_fanAB3_add_rest]
    exact hTwoD
  exact (smul_add_lower_ne_C410 (-(1280 : k)) (2048 * k2)
    (A * B ^ 3)
    (lWallFanRestTwoAB3_410 0 beta gamma delta zeta eta theta A B U)
    (A.natDegree + 3 * B.natDegree) (by norm_num)
    (mul_ne_zero hA (pow_ne_zero 3 hB)) (by omega)
    (by rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]) hrest) heq

theorem scaleZeroBU2RestTwo410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hA4 : 4 * A.natDegree < B.natDegree + 2 * U.natDegree)
    (hAB3 : A.natDegree + 3 * B.natDegree <
      B.natDegree + 2 * U.natDegree) :
    (lWallFanRestTwoBU2_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        B.natDegree + 2 * U.natDegree := by
  simp only [lWallFanRestTwoBU2_410, lWallIntermediateRestTwo410,
    mul_zero, neg_zero, zero_smul, zero_add, add_zero]
  compute_degree
  omega

theorem scaleZero_BU2_open_chamber_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hA4 : 4 * A.natDegree < B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree)
    (hAB3 : A.natDegree + 3 * B.natDegree < B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hUne : U ≠ 0 := by simpa only [U] using hU
  have hrest : (lWallFanRestTwoBU2_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        B.natDegree + 2 * U.natDegree := by
    apply scaleZeroBU2RestTwo410_natDegree_lt
    · exact hBpos
    · simpa only [U] using hA4
    · simpa only [U] using hAB3
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have heq : (480 : k) • (B * U ^ 2) +
      lWallFanRestTwoBU2_410
        0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    rw [← discriminantInvariantTwoNumerator410_eq_fanBU2_add_rest]
    exact hTwoD
  exact (smul_add_lower_ne_C410 (480 : k) (2048 * k2) (B * U ^ 2)
    (lWallFanRestTwoBU2_410 0 beta gamma delta zeta eta theta A B U)
    (B.natDegree + 2 * U.natDegree) (by norm_num)
    (mul_ne_zero hB (pow_ne_zero 2 hUne)) (by omega)
    (by rw [natDegree_mul hB (pow_ne_zero 2 hUne), natDegree_pow]) hrest) heq

def ScaleZeroI2TriangleTie410 (A B U : k[X]) : Prop :=
  (4 * A.natDegree = A.natDegree + 3 * B.natDegree ∧
      B.natDegree + 2 * U.natDegree ≤ 4 * A.natDegree) ∨
    (4 * A.natDegree = B.natDegree + 2 * U.natDegree ∧
      A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree) ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree)

/-- Away from the two coordinate degeneracies, the scale-zero second
invariant confines the positive-`B` beta packet to its three exact tropical
tie walls. -/
theorem scaleZero_positiveBeta_I2_triangle_classification
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hBpos : 0 < B.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) :
    A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      ScaleZeroI2TriangleTie410 A B (A ^ 2 - (4 : k) • C0) := by
  by_cases hA : A = 0
  · exact Or.inl hA
  by_cases hU : A ^ 2 - (4 : k) • C0 = 0
  · exact Or.inr (Or.inl hU)
  right
  right
  have hA4raw := scaleZero_positiveBeta_A4_degree_fan_wall
    beta gamma delta zeta eta theta k2 A B C0 hbeta hTwo
  have hA4 : 4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree ∨
      4 * A.natDegree ≤ B.natDegree +
        2 * (A ^ 2 - (4 : k) • C0).natDegree := by
    rcases hA4raw with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by omega)
  have hAB3 : A.natDegree + 3 * B.natDegree ≤ 4 * A.natDegree ∨
      A.natDegree + 3 * B.natDegree ≤ B.natDegree +
        2 * (A ^ 2 - (4 : k) • C0).natDegree := by
    by_contra hnot
    push_neg at hnot
    exact scaleZero_AB3_open_chamber_impossible
      beta gamma delta zeta eta theta k2 A B C0 hA hBpos
        hnot.1 hnot.2 hTwo
  have hBU2 : B.natDegree +
        2 * (A ^ 2 - (4 : k) • C0).natDegree ≤ 4 * A.natDegree ∨
      B.natDegree + 2 * (A ^ 2 - (4 : k) • C0).natDegree ≤
        A.natDegree + 3 * B.natDegree := by
    by_contra hnot
    push_neg at hnot
    exact scaleZero_BU2_open_chamber_impossible
      beta gamma delta zeta eta theta k2 A B C0 hU hBpos
        hnot.1 hnot.2 hTwo
  simp only [ScaleZeroI2TriangleTie410]
  omega

/-! ## Source-facing triangle packet -/

def TriangleFanPositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FanRestrictedPositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    (A = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      ScaleZeroI2TriangleTie410 A B (A ^ 2 - (4 : k) • C0))

def TriangleFanPositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      TriangleFanPositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_triangleFanPositiveB_earlyLoad_residual
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
      TriangleFanPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_fanRestrictedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    rcases hbeta with ⟨hbeta, hB, hfan⟩
    refine ⟨hbeta, hB, hfan, ?_⟩
    apply scaleZero_positiveBeta_I2_triangle_classification
      beta gamma delta zeta eta theta k2 A B C0 hbeta
        hfan.1.2.2.2.2
    simpa [hold.1] using hTwo
  · exact Or.inr hlater

theorem integrated410_triangleFanPositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      TriangleFanPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_triangleFanPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_triangleFanPositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          TriangleFanPositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_triangleFanPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end PositiveBTriangleFan410

end Max11DegreeRoutes
