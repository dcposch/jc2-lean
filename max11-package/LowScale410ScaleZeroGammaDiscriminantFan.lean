import LowScale410ScaleZeroNonzeroGammaCone

/-!
# Discriminant-core refinement of the gamma Newton packet

The two raw gamma faces factor exactly as

`-(3/4) gamma · B U`, `(3/32) gamma · (U^2 - 8 A B^2)`

for `U=A^2-4C0`.  Under `gamma≠0`, this converts the raw Newton packet into
an exact discriminant-coordinate fan: the first face is either on a
coordinate wall, degree-zero in both factors, or tied against the zero/later
competition; the second is on the explicit gamma core wall, degree zero, or
tied against its competition.  Later loads remain arbitrary.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaDiscriminantFan410

variable {k : Type*} [Field k] [CharZero k]

theorem gammaLoadTwoPolynomial410_eq_discriminantCore
    (gamma : k) (A B C0 : k[X]) :
    gammaLoadTwoPolynomial410 gamma A B C0 =
      (-(3 / 4 * gamma) : k) • gammaLoadTwoCorePolynomial410 A B C0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [gammaLoadTwoPolynomial410, gammaLoadTwoCorePolynomial410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul]
  ring

theorem gammaLoadOnePolynomial410_eq_discriminantCore
    (gamma : k) (A B C0 : k[X]) :
    gammaLoadOnePolynomial410 gamma A B C0 =
      (3 / 32 * gamma : k) • gammaLoadOneCorePolynomial410 A B C0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [gammaLoadOnePolynomial410, gammaLoadOneCorePolynomial410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul]
  ring

def DiscriminantGammaNewtonResidual410
    (delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (B = 0 ∨ A ^ 2 - (4 : k) • C0 = 0 ∨
      (B.natDegree = 0 ∧
        (A ^ 2 - (4 : k) • C0).natDegree = 0) ∨
      B.natDegree + (A ^ 2 - (4 : k) • C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterTwoRest410 delta zeta eta theta A B C0).natDegree) ∧
    (gammaLoadOneCorePolynomial410 A B C0 = 0 ∨
      (gammaLoadOneCorePolynomial410 A B C0).natDegree = 0 ∨
      (gammaLoadOneCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

theorem nonzeroGammaNewtonResidual410_discriminant_refinement
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hgamma : gamma ≠ 0)
    (hold : NonzeroGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    DiscriminantGammaNewtonResidual410 delta zeta eta theta A B C0 := by
  have hcTwo : (-(3 / 4 * gamma) : k) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (by norm_num) hgamma)
  have hcOne : (3 / 32 * gamma : k) ≠ 0 :=
    mul_ne_zero (by norm_num) hgamma
  constructor
  · rcases hold.1 with hzero | hdegree | hcompetition
    · rw [gammaLoadTwoPolynomial410_eq_discriminantCore] at hzero
      have hcore : gammaLoadTwoCorePolynomial410 A B C0 = 0 :=
        (smul_eq_zero.mp hzero).resolve_left hcTwo
      simp only [gammaLoadTwoCorePolynomial410] at hcore
      rcases mul_eq_zero.mp hcore with hB | hU
      · exact Or.inl hB
      · exact Or.inr (Or.inl hU)
    · by_cases hB : B = 0
      · exact Or.inl hB
      right
      by_cases hU : A ^ 2 - (4 : k) • C0 = 0
      · exact Or.inl hU
      right
      left
      have hdegree' : B.natDegree +
          (A ^ 2 - (4 : k) • C0).natDegree = 0 := by
        rw [gammaLoadTwoPolynomial410_eq_discriminantCore,
          natDegree_smul _ hcTwo, gammaLoadTwoCorePolynomial410,
          natDegree_mul hB hU] at hdegree
        exact hdegree
      exact ⟨by omega, by omega⟩
    · by_cases hB : B = 0
      · exact Or.inl hB
      right
      by_cases hU : A ^ 2 - (4 : k) • C0 = 0
      · exact Or.inl hU
      right
      right
      rw [gammaLoadTwoPolynomial410_eq_discriminantCore,
        natDegree_smul _ hcTwo, gammaLoadTwoCorePolynomial410,
        natDegree_mul hB hU] at hcompetition
      exact hcompetition
  · rcases hold.2 with hzero | hdegree | hcompetition
    · rw [gammaLoadOnePolynomial410_eq_discriminantCore] at hzero
      exact Or.inl ((smul_eq_zero.mp hzero).resolve_left hcOne)
    · right
      left
      rw [gammaLoadOnePolynomial410_eq_discriminantCore,
        natDegree_smul _ hcOne] at hdegree
      exact hdegree
    · right
      right
      rw [gammaLoadOnePolynomial410_eq_discriminantCore,
        natDegree_smul _ hcOne] at hcompetition
      exact hcompetition

/-! ## Source-facing discriminant gamma packet -/

def GammaDiscriminantNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DiscriminantGammaNewtonResidual410 delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaDiscriminantNoncubic_earlyLoad_residual
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
      GammaDiscriminantNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaNewtonNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      nonzeroGammaNewtonResidual410_discriminant_refinement
        gamma delta zeta eta theta A B C0 hgamma.2.1 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaDiscriminantNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaDiscriminantNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaDiscriminantNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaDiscriminantNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaDiscriminantNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaDiscriminantNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaDiscriminantFan410

end Max11DegreeRoutes
