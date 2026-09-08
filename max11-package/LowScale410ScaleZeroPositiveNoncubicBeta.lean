import LowScale410ScaleZeroNoncubicBetaDegreeZero

/-!
# The positive genuine noncubic beta packet

This file resolves the constant-`B` degree chambers inside the remaining
positive noncubic beta packet.  The first invariant excludes both unbalanced
cones.  On the balanced cone its top zero-load face is exactly
`-(5/256) (A^2-4C0)^3`, so the no-drop chamber is excluded as well.  Hence a
constant nonzero `B` survivor must lie on the sharp dropped-discriminant wall.
Later loads remain arbitrary and strictly below the faces used here.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section PositiveNoncubicBeta410

variable {k : Type*} [Field k] [CharZero k]

/-! ## The two unbalanced constant-`B` cones -/

/-- Everything except the `A^6` face of `I1`. -/
def noncubicBetaAHighOneRest410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (15 / 64 : k) • (A ^ 4 * C0) +
    (15 / 32 : k) • (A ^ 3 * B ^ 2) -
    (15 / 16 : k) • (A ^ 2 * C0 ^ 2) -
    (15 / 8 : k) • (A * B ^ 2 * C0) - (5 / 32 : k) • B ^ 4 +
    (5 / 4 : k) • C0 ^ 3 + betaLoadOnePolynomial410 beta A B C0 +
      betaLoadOneRest410 gamma delta zeta eta theta A B C0

theorem firstIntegralOne410_eq_Asix_add_AHigh_rest
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    firstIntegralOnePolynomial410 0 beta gamma delta zeta eta theta
        A B C0 =
      -(5 / 256 : k) • A ^ 6 +
        noncubicBetaAHighOneRest410
          beta gamma delta zeta eta theta A B C0 := by
  rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
    loadCorrectionOnePolynomial410_eq_beta_add_rest, zeroLoadOne410_eq]
  simp only [noncubicBetaAHighOneRest410]
  abel

theorem noncubicBetaAHighOneRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hClow : C0.natDegree < 2 * A.natDegree) :
    (noncubicBetaAHighOneRest410
      beta gamma delta zeta eta theta A B C0).natDegree <
        6 * A.natDegree := by
  simp only [noncubicBetaAHighOneRest410, betaLoadOnePolynomial410,
    betaLoadOneRest410]
  compute_degree
  omega

theorem noncubicBeta_constantB_AHigh_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hClow : C0.natDegree < 2 * A.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hrest := noncubicBetaAHighOneRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hApos hB0 hClow
  have hfaceDeg : (A ^ 6).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow]
  have heq :
      -(5 / 256 : k) • A ^ 6 +
          noncubicBetaAHighOneRest410
            beta gamma delta zeta eta theta A B C0 = C k1 := by
    rw [← firstIntegralOne410_eq_Asix_add_AHigh_rest]
    exact hOne
  exact (smul_add_lower_ne_C410 (-(5 / 256 : k)) k1 (A ^ 6)
    (noncubicBetaAHighOneRest410
      beta gamma delta zeta eta theta A B C0)
    (6 * A.natDegree) (by norm_num) (pow_ne_zero 6 hA)
    (by omega) hfaceDeg hrest) heq

theorem noncubicBetaConstantAOneRest410_natDegree_lt_CHigh
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hB0 : B.natDegree = 0)
    (hChigh : 2 * A.natDegree < C0.natDegree) :
    (noncubicBetaConstantAOneRest410
      beta gamma delta zeta eta theta A B C0).natDegree <
        3 * C0.natDegree := by
  simp only [noncubicBetaConstantAOneRest410, betaLoadOnePolynomial410,
    betaLoadOneRest410]
  compute_degree
  omega

theorem noncubicBeta_constantB_CHigh_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hB0 : B.natDegree = 0)
    (hChigh : 2 * A.natDegree < C0.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hCpos : 0 < C0.natDegree := by omega
  have hC0 : C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hCpos
    omega
  have hrest := noncubicBetaConstantAOneRest410_natDegree_lt_CHigh
    beta gamma delta zeta eta theta A B C0 hB0 hChigh
  have hfaceDeg : (C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_pow]
  have heq :
      (5 / 4 : k) • C0 ^ 3 +
          noncubicBetaConstantAOneRest410
            beta gamma delta zeta eta theta A B C0 = C k1 := by
    rw [← firstIntegralOne410_eq_Ccube_add_constantA_rest]
    exact hOne
  exact (smul_add_lower_ne_C410 (5 / 4 : k) k1 (C0 ^ 3)
    (noncubicBetaConstantAOneRest410
      beta gamma delta zeta eta theta A B C0)
    (3 * C0.natDegree) (by norm_num) (pow_ne_zero 3 hC0)
    (by omega) hfaceDeg hrest) heq

/-! ## The balanced no-drop cone -/

theorem betaCubicBalancedStrictOneFace410_eq_discriminantCube
    (A C0 : k[X]) :
    betaCubicBalancedStrictOneFace410 A C0 =
      -(5 / 256 : k) • (A ^ 2 - (4 : k) • C0) ^ 3 := by
  have hface :
      firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A 0 C0 =
        betaCubicBalancedStrictOneFace410 A C0 := by
    rw [zeroLoadOne410_eq]
    simp [betaCubicBalancedStrictOneFace410]
  have hscale := firstIntegralOnePolynomial410_zeroLoad_of_B A C0
  rw [hface] at hscale
  calc
    betaCubicBalancedStrictOneFace410 A C0 =
        (1 / 256 : k) •
          ((256 : k) • betaCubicBalancedStrictOneFace410 A C0) := by
            module
    _ = (1 / 256 : k) •
        (-(5 : k) • (A ^ 2 - (4 : k) • C0) ^ 3) := by rw [hscale]
    _ = -(5 / 256 : k) • (A ^ 2 - (4 : k) • C0) ^ 3 := by module

theorem noncubicBeta_constantB_balanced_nodrop_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hnodrop : A.leadingCoeff ^ 2 ≠ 4 * C0.leadingCoeff)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hC0 : C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hbalanced
    omega
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hUdeg : U.natDegree = 2 * A.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · dsimp only [U]
      exact (natDegree_sub_le _ _).trans <| max_le
        (by rw [natDegree_pow])
        (by rw [natDegree_smul C0 (by norm_num : (4 : k) ≠ 0), hbalanced])
    · dsimp only [U]
      have hA2 : (A ^ 2).coeff (2 * A.natDegree) =
          A.leadingCoeff ^ 2 := by
        have hdeg : (A ^ 2).natDegree = 2 * A.natDegree := by
          rw [natDegree_pow]
        rw [← hdeg, coeff_natDegree, leadingCoeff_pow]
      have h4C : ((4 : k) • C0).coeff (2 * A.natDegree) =
          4 * C0.leadingCoeff := by
        rw [coeff_smul, smul_eq_mul, ← hbalanced, coeff_natDegree]
      rw [coeff_sub, hA2, h4C]
      exact sub_ne_zero.mpr hnodrop
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUdeg
    omega
  have hrest := noncubicBetaBalancedOneRest410_natDegree_lt
    beta gamma delta zeta eta theta A B C0 hApos hB0 hbalanced
  have hfaceDeg : (U ^ 3).natDegree = 6 * A.natDegree := by
    rw [natDegree_pow, hUdeg]
    omega
  have heq :
      -(5 / 256 : k) • U ^ 3 +
          noncubicBetaBalancedOneRest410
            beta gamma delta zeta eta theta A B C0 = C k1 := by
    rw [← betaCubicBalancedStrictOneFace410_eq_discriminantCube]
    rw [← firstIntegralOne410_eq_noncubicBalancedFace_add_rest]
    exact hOne
  exact (smul_add_lower_ne_C410 (-(5 / 256 : k)) k1 (U ^ 3)
    (noncubicBetaBalancedOneRest410
      beta gamma delta zeta eta theta A B C0)
    (6 * A.natDegree) (by norm_num) (pow_ne_zero 3 hU)
    (by omega) hfaceDeg hrest) heq

/-- Sharp classification of the constant-`B`, positive beta face: it must
be balanced and its discriminant leading coefficient must drop. -/
theorem positiveNoncubicBeta_constantB_forces_discriminant_drop
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hB0 : B.natDegree = 0)
    (hpositive : 0 < B.natDegree +
      (betaOneCorePolynomial410 A B C0).natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) :
    0 < A.natDegree ∧
      C0.natDegree = 2 * A.natDegree ∧
      A.leadingCoeff ^ 2 = 4 * C0.leadingCoeff := by
  have hApos : 0 < A.natDegree := by
    by_contra hnot
    have hA0 : A.natDegree = 0 := by omega
    by_cases hCpos : 0 < C0.natDegree
    · exact (noncubicBeta_degreeZero_constantA_C_positive_impossible
        beta gamma delta zeta eta theta k1 A B C0 hA0 hB0 hCpos hOne).elim
    · have hcore0 :
          (betaOneCorePolynomial410 A B C0).natDegree = 0 := by
        have hcorele :
            (betaOneCorePolynomial410 A B C0).natDegree ≤ 0 := by
          simp only [betaOneCorePolynomial410]
          compute_degree
          omega
        omega
      omega
  refine ⟨hApos, ?_⟩
  rcases lt_trichotomy C0.natDegree (2 * A.natDegree) with hlow | heq | hhigh
  · exact (noncubicBeta_constantB_AHigh_impossible
      beta gamma delta zeta eta theta k1 A B C0
        hApos hB0 hlow hOne).elim
  · refine ⟨heq, ?_⟩
    by_contra hnodrop
    exact noncubicBeta_constantB_balanced_nodrop_impossible
      beta gamma delta zeta eta theta k1 A B C0
        hApos hB0 heq hnodrop hOne
  · exact (noncubicBeta_constantB_CHigh_impossible
      beta gamma delta zeta eta theta k1 A B C0
        hB0 hhigh hOne).elim

/-! ## Refined packet and source transport -/

def DroppedNoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (betaTwoCorePolynomial410 A B C0 = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree) ∧
    betaOneCorePolynomial410 A B C0 ≠ 0 ∧
      0 < B.natDegree +
        (betaOneCorePolynomial410 A B C0).natDegree ∧
      B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree ∧
      (0 < B.natDegree ∨
        (B.natDegree = 0 ∧ 0 < A.natDegree ∧
          C0.natDegree = 2 * A.natDegree ∧
          A.leadingCoeff ^ 2 = 4 * C0.leadingCoeff))

def DroppedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      DroppedNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_droppedNoncubic_earlyLoad_residual
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
      DroppedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_degreeZeroDeleted_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    refine ⟨hbeta.1, hbeta.2.1, hbeta.2.2.1, hbeta.2.2.2.1,
      hbeta.2.2.2.2.1, hbeta.2.2.2.2.2, ?_⟩
    by_cases hBpos : 0 < B.natDegree
    · exact Or.inl hBpos
    · right
      have hB0 : B.natDegree = 0 := by omega
      have hOne0 : firstIntegralOnePolynomial410
          0 beta gamma delta zeta eta theta A B C0 = C k1 := by
        simpa [hold.1] using hOne
      exact ⟨hB0, positiveNoncubicBeta_constantB_forces_discriminant_drop
        beta gamma delta zeta eta theta k1 A B C0 hB0
          hbeta.2.2.2.2.1 hOne0⟩
  · exact Or.inr hlater

theorem integrated410_droppedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      DroppedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_droppedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_droppedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          DroppedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_droppedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end PositiveNoncubicBeta410

end Max11DegreeRoutes
