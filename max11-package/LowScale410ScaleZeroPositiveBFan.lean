import LowScale410ScaleZeroConstantBDropElimination

/-!
# The positive-`B` scale-zero beta fan

For the surviving genuine noncubic beta packet, `deg B > 0`.  Two open
Newton chambers can be deleted without imposing any condition on the later
loads.  If `B` has degree strictly above both `A` and the discriminant
coordinate `U = A^2 - 4 C0`, then `B^4` is the unique top monomial of the
first invariant.  At the opposite exposed vertex, the beta monomial `A^4`
is uniquely top in the second invariant.  Their complements give an exact
smaller fan packet for the next elimination step.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section PositiveBFan410

variable {k : Type*} [Field k] [CharZero k]

theorem scaleZeroB4RestOne410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hA_lt : A.natDegree < B.natDegree)
    (hU_lt : U.natDegree < B.natDegree) :
    (lWallFanRestOneB4_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        4 * B.natDegree := by
  simp only [lWallFanRestOneB4_410, lWallLowURestOne410, mul_zero,
    neg_zero, zero_smul, zero_add, add_zero]
  compute_degree
  omega

/-- The scale-zero `B^4` vertex excludes an open chamber, independently of
all five later loads. -/
theorem scaleZero_positiveB_B4_open_chamber_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree)
    (hA_lt : A.natDegree < B.natDegree)
    (hU_lt : (A ^ 2 - (4 : k) • C0).natDegree < B.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hrest : (lWallFanRestOneB4_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        4 * B.natDegree := by
    apply scaleZeroB4RestOne410_natDegree_lt
    · exact hBpos
    · exact hA_lt
    · simpa only [U] using hU_lt
  have hOneD : discriminantInvariantOneNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have heq : -(320 : k) • B ^ 4 +
      lWallFanRestOneB4_410
        0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    rw [← discriminantInvariantOneNumerator410_eq_fanB4_add_rest]
    exact hOneD
  exact (smul_add_lower_ne_C410 (-(320 : k)) (2048 * k1) (B ^ 4)
    (lWallFanRestOneB4_410 0 beta gamma delta zeta eta theta A B U)
    (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB) (by omega)
    (by rw [natDegree_pow]) hrest) heq

theorem scaleZero_positiveB_B_degree_fan_wall
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) :
    B.natDegree ≤ max A.natDegree
      (A ^ 2 - (4 : k) • C0).natDegree := by
  by_contra hnot
  have hA_lt : A.natDegree < B.natDegree := by omega
  have hU_lt : (A ^ 2 - (4 : k) • C0).natDegree < B.natDegree := by
    omega
  exact scaleZero_positiveB_B4_open_chamber_impossible
    beta gamma delta zeta eta theta k1 A B C0 hBpos hA_lt hU_lt hOne

theorem positiveBA4RestTwo410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hAB3 : A.natDegree + 3 * B.natDegree < 4 * A.natDegree)
    (hBU2 : B.natDegree + 2 * U.natDegree < 4 * A.natDegree)
    (hU : U.natDegree < 2 * A.natDegree) :
    (constantBDropTwoRest410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [constantBDropTwoRest410]
  compute_degree
  omega

/-- The beta `A^4` vertex deletes the opposite open chamber of the second
invariant, again with arbitrary later loads. -/
theorem scaleZero_positiveBeta_A4_open_chamber_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0)
    (hAB3 : A.natDegree + 3 * B.natDegree < 4 * A.natDegree)
    (hBU2 : B.natDegree +
      2 * (A ^ 2 - (4 : k) • C0).natDegree < 4 * A.natDegree)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree < 2 * A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hApos : 0 < A.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hrest : (constantBDropTwoRest410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
    apply positiveBA4RestTwo410_natDegree_lt
    · exact hAB3
    · simpa only [U] using hBU2
    · simpa only [U] using hU
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have heq : (140 * beta : k) • A ^ 4 +
      constantBDropTwoRest410
        beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    rw [← discriminantInvariantTwo410_eq_constantBDrop_face_add_rest]
    exact hTwoD
  exact (smul_add_lower_ne_C410 (140 * beta : k) (2048 * k2) (A ^ 4)
    (constantBDropTwoRest410 beta gamma delta zeta eta theta A B U)
    (4 * A.natDegree) (mul_ne_zero (by norm_num) hbeta)
    (pow_ne_zero 4 hA) (by omega) (by rw [natDegree_pow]) hrest) heq

theorem scaleZero_positiveBeta_A4_degree_fan_wall
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) :
    4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree ∨
      4 * A.natDegree ≤ B.natDegree +
        2 * (A ^ 2 - (4 : k) • C0).natDegree ∨
      2 * A.natDegree ≤ (A ^ 2 - (4 : k) • C0).natDegree := by
  by_contra hnot
  push_neg at hnot
  exact scaleZero_positiveBeta_A4_open_chamber_impossible
    beta gamma delta zeta eta theta k2 A B C0 hbeta
      (by omega) (by omega) (by omega) hTwo

/-! ## Fan-restricted beta packet and source transport -/

def FanRestrictedPositiveBNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  PositiveBNoncubicBetaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    B.natDegree ≤ max A.natDegree
      (A ^ 2 - (4 : k) • C0).natDegree ∧
    (4 * A.natDegree ≤ A.natDegree + 3 * B.natDegree ∨
      4 * A.natDegree ≤ B.natDegree +
        2 * (A ^ 2 - (4 : k) • C0).natDegree ∨
      2 * A.natDegree ≤ (A ^ 2 - (4 : k) • C0).natDegree)

def FanRestrictedPositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      FanRestrictedPositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_fanRestrictedPositiveB_earlyLoad_residual
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
      FanRestrictedPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_positiveBNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    refine ⟨hbeta.1, hbeta.2.1, hbeta.2.2, ?_, ?_⟩
    · apply scaleZero_positiveB_B_degree_fan_wall
        beta gamma delta zeta eta theta k1 A B C0 hbeta.2.2.2.2.2.2
      simpa [hold.1] using hOne
    · apply scaleZero_positiveBeta_A4_degree_fan_wall
        beta gamma delta zeta eta theta k2 A B C0 hbeta.1
      simpa [hold.1] using hTwo
  · exact Or.inr hlater

theorem integrated410_fanRestrictedPositiveB_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      FanRestrictedPositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_fanRestrictedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_fanRestrictedPositiveB_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          FanRestrictedPositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_fanRestrictedPositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end PositiveBFan410

end Max11DegreeRoutes
