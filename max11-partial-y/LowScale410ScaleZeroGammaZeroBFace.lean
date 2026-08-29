import LowScale410ScaleZeroGammaZeroAFace

/-!
# Deletion of the `U=0, B=0` gamma coordinate face

Here `C0=A^2/4`, and the first conserved polynomial becomes exactly
`(5/32) delta A^3 + (3/8) zeta A^2 + theta A`.  Its highest nonzero load
excludes positive-degree `A`.  If only `eta` remains, the terminal `W`
coefficient vanishes; constant `A` is already excluded by the terminal row.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaZeroBFace410

variable {k : Type*} [Field k] [CharZero k]

theorem firstIntegralTwo410_zeroB_discriminantZero_specialization
    (gamma delta zeta eta theta : k) (A : k[X]) :
    firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A 0 ((1 / 4 : k) • A ^ 2) =
      (5 / 32 * delta : k) • A ^ 3 +
        (3 / 8 * zeta : k) • A ^ 2 + theta • A := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [firstIntegralTwoPolynomial410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_zero,
    map_mul]
  ring

theorem integratedW410_zeroB_discriminantZero_specialization
    (alpha gamma delta epsilon zeta theta : k) (A : k[X]) :
    integratedWPolynomial410
        0 alpha 0 gamma delta epsilon zeta theta
          A 0 ((1 / 4 : k) • A ^ 2) =
      (15 / 32 * delta : k) • A ^ 2 +
        (3 / 4 * zeta : k) • A + C theta := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [integratedWPolynomial410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_zero,
    map_mul]
  ring

theorem gammaCoordinate_U_zero_B_zero_impossible
    (alpha gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0) (hB : B = 0)
    (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hAC : A ^ 2 = (4 : k) • C0 := sub_eq_zero.mp hU
  have hC0 : C0 = (1 / 4 : k) • A ^ 2 := by
    calc
      C0 = (1 / 4 : k) • ((4 : k) • C0) := by module
      _ = (1 / 4 : k) • A ^ 2 := by rw [← hAC]
  subst B
  subst C0
  rw [firstIntegralTwo410_zeroB_discriminantZero_specialization] at hTwo
  by_cases hA0 : A.natDegree = 0
  · have hCdegree : ((1 / 4 : k) • A ^ 2).natDegree = 0 := by
      rw [natDegree_smul _ (by norm_num), natDegree_pow, hA0]
    exact betaCubicWall_balanced_constants_impossible
      alpha 0 gamma delta epsilon zeta eta theta iota terminal
        A 0 ((1 / 4 : k) • A ^ 2) hA0 rfl hCdegree
        hterminal hLower
  · have hApos : 0 < A.natDegree := by omega
    have hAne : A ≠ 0 := by
      intro hzero
      subst A
      exact hA0 natDegree_zero
    by_cases hdelta : delta = 0
    · by_cases hzeta : zeta = 0
      · by_cases htheta : theta = 0
        · have hW : integratedWPolynomial410
              0 alpha 0 gamma delta epsilon zeta theta A 0
                ((1 / 4 : k) • A ^ 2) = 0 := by
            rw [integratedW410_zeroB_discriminantZero_specialization]
            simp [hdelta, hzeta, htheta]
          have hzero : lowerRowZeroPolynomial410
              (integratedWPolynomial410
                0 alpha 0 gamma delta epsilon zeta theta A 0
                  ((1 / 4 : k) • A ^ 2))
              (integratedZPolynomial410
                0 alpha 0 gamma delta epsilon zeta eta iota A 0
                  ((1 / 4 : k) • A ^ 2))
              0 ((1 / 4 : k) • A ^ 2) = 0 := by
            rw [hW]
            simp [lowerRowZeroPolynomial410]
          rw [hzero] at hLower
          exact hterminal (C_eq_zero.mp hLower.symm)
        · have hthetaNe : theta ≠ 0 := htheta
          have hlinear : theta • A = C k2 := by
            simpa [hdelta, hzeta] using hTwo
          have hdegree := congrArg Polynomial.natDegree hlinear
          rw [natDegree_smul A hthetaNe, natDegree_C] at hdegree
          omega
      · let R : k[X] := theta • A
        have hform : (3 / 8 * zeta : k) • A ^ 2 + R = C k2 := by
          simpa [hdelta, R] using hTwo
        have hrest : R.natDegree < 2 * A.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        exact (smul_add_lower_ne_C410 (3 / 8 * zeta : k) k2 (A ^ 2) R
          (2 * A.natDegree) (mul_ne_zero (by norm_num) hzeta)
          (pow_ne_zero 2 hAne) (by omega) (by rw [natDegree_pow])
          hrest) hform
    · let R : k[X] :=
          (3 / 8 * zeta : k) • A ^ 2 + theta • A
      have hform : (5 / 32 * delta : k) • A ^ 3 + R = C k2 := by
        simpa [R, add_assoc] using hTwo
      have hrest : R.natDegree < 3 * A.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      exact (smul_add_lower_ne_C410 (5 / 32 * delta : k) k2 (A ^ 3) R
        (3 * A.natDegree) (mul_ne_zero (by norm_num) hdelta)
        (pow_ne_zero 3 hAne) (by omega) (by rw [natDegree_pow]) hrest) hform

def ZeroBDeletedGammaNewtonResidual410
    (delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  ZeroADeletedGammaNewtonResidual410 delta zeta eta theta A B C0 ∧
    ¬ (A ^ 2 - (4 : k) • C0 = 0 ∧ B = 0)

theorem zeroADeletedGammaNewtonResidual410_zeroB_refinement
    (alpha gamma delta epsilon zeta eta theta iota k2 terminal : k)
    (A B C0 : k[X])
    (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hold : ZeroADeletedGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    ZeroBDeletedGammaNewtonResidual410 delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  rintro ⟨hU, hB⟩
  exact gammaCoordinate_U_zero_B_zero_impossible
    alpha gamma delta epsilon zeta eta theta iota k2 terminal A B C0
      hU hB hterminal hTwo hLower

theorem zeroBDeletedGammaNewtonResidual410_zeroU_competition
    (alpha gamma delta epsilon zeta eta theta iota k1 terminal : k)
    (A B C0 : k[X])
    (hterminal : terminal ≠ 0)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal)
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hold : ZeroBDeletedGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    A.natDegree + 2 * B.natDegree ≤
      max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
  rcases zeroADeletedGammaNewtonResidual410_zeroU_selector
      alpha gamma delta epsilon zeta eta theta iota k1 terminal A B C0
        hterminal hOne hLower hU hold.1 with hB | hcompetition
  · exact (hold.2 ⟨hU, hB⟩).elim
  · exact hcompetition

/-! ## Constant, integrated, and normalized source wrappers -/

def GammaZeroBDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      ZeroBDeletedGammaNewtonResidual410
        delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaZeroBDeletedNoncubic_earlyLoad_residual
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
      GammaZeroBDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaZeroADeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
          iota A B C0) B C0 = C terminal := by
      simpa [hold.1, hgamma.1] using hLower
    left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      zeroADeletedGammaNewtonResidual410_zeroB_refinement
        alpha gamma delta epsilon zeta eta theta iota k2 terminal
          A B C0 hterminal hTwo0 hLower0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaZeroBDeletedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaZeroBDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaZeroBDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaZeroBDeletedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaZeroBDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaZeroBDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaZeroBFace410

end Max11DegreeRoutes
