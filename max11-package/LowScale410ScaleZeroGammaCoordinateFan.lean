import LowScale410ScaleZeroGammaDiscriminantFan

/-!
# Coordinate refinement of the nonzero-gamma fan

The second clean gamma face is `U^2 - 8 A B^2`, where
`U=A^2-4C0`.  Consequently, on the first-face alternatives `B=0` and
`U=0`, its Newton residual gives a strictly smaller exact fan.  This file
records that refinement while leaving every later-load competition term
unchanged.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaCoordinateFan410

variable {k : Type*} [Field k] [CharZero k]

def GammaSecondCoreResidual410
    (delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  gammaLoadOneCorePolynomial410 A B C0 = 0 ∨
    (gammaLoadOneCorePolynomial410 A B C0).natDegree = 0 ∨
    (gammaLoadOneCorePolynomial410 A B C0).natDegree ≤
      max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree

theorem gammaSecondCoreResidual410_zeroB_refinement
    (delta zeta eta theta : k) (A B C0 : k[X])
    (hB : B = 0)
    (hold : GammaSecondCoreResidual410 delta zeta eta theta A B C0) :
    A ^ 2 - (4 : k) • C0 = 0 ∨
      (A ^ 2 - (4 : k) • C0).natDegree = 0 ∨
      2 * (A ^ 2 - (4 : k) • C0).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
  rcases hold with hzero | hdegree | hcompetition
  · left
    have hsquare : (A ^ 2 - (4 : k) • C0) ^ 2 = 0 := by
      simpa [gammaLoadOneCorePolynomial410, hB] using hzero
    exact eq_zero_of_pow_eq_zero hsquare
  · right
    left
    have hsquare : ((A ^ 2 - (4 : k) • C0) ^ 2).natDegree = 0 := by
      simpa [gammaLoadOneCorePolynomial410, hB] using hdegree
    rw [natDegree_pow] at hsquare
    omega
  · right
    right
    have hsquare : ((A ^ 2 - (4 : k) • C0) ^ 2).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
      simpa [gammaLoadOneCorePolynomial410, hB] using hcompetition
    rw [natDegree_pow] at hsquare
    exact hsquare

theorem gammaSecondCoreResidual410_zeroU_refinement
    (delta zeta eta theta : k) (A B C0 : k[X])
    (hU : A ^ 2 - (4 : k) • C0 = 0)
    (hold : GammaSecondCoreResidual410 delta zeta eta theta A B C0) :
    A = 0 ∨ B = 0 ∨ (A.natDegree = 0 ∧ B.natDegree = 0) ∨
      A.natDegree + 2 * B.natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
  rcases hold with hzero | hdegree | hcompetition
  · have hscaled : (8 : k) • (A * B ^ 2) = 0 := by
      simpa [gammaLoadOneCorePolynomial410, hU] using hzero
    have hproduct : A * B ^ 2 = 0 :=
      (smul_eq_zero.mp hscaled).resolve_left (by norm_num)
    rcases mul_eq_zero.mp hproduct with hA | hBpow
    · exact Or.inl hA
    · exact Or.inr (Or.inl (eq_zero_of_pow_eq_zero hBpow))
  · by_cases hA : A = 0
    · exact Or.inl hA
    right
    by_cases hB : B = 0
    · exact Or.inl hB
    right
    left
    have hproduct : (A * B ^ 2).natDegree = 0 := by
      have hscaled : ((-(8 : k)) • (A * B ^ 2)).natDegree = 0 := by
        simpa [gammaLoadOneCorePolynomial410, hU] using hdegree
      rw [natDegree_smul _ (by norm_num)] at hscaled
      exact hscaled
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow] at hproduct
    exact ⟨by omega, by omega⟩
  · by_cases hA : A = 0
    · exact Or.inl hA
    right
    by_cases hB : B = 0
    · exact Or.inl hB
    right
    right
    have hproduct : (A * B ^ 2).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
      have hscaled : ((-(8 : k)) • (A * B ^ 2)).natDegree ≤
          max
            (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
            (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree := by
        simpa [gammaLoadOneCorePolynomial410, hU] using hcompetition
      rw [natDegree_smul _ (by norm_num)] at hscaled
      exact hscaled
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow] at hproduct
    exact hproduct

def CoordinateGammaNewtonResidual410
    (delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (((B = 0 ∧
        (A ^ 2 - (4 : k) • C0 = 0 ∨
          (A ^ 2 - (4 : k) • C0).natDegree = 0 ∨
          2 * (A ^ 2 - (4 : k) • C0).natDegree ≤
            max
              (firstIntegralOnePolynomial410
                0 0 0 0 0 0 0 A B C0).natDegree
              (gammaLaterOneRest410
                delta zeta eta theta A B C0).natDegree)) ∨
      (A ^ 2 - (4 : k) • C0 = 0 ∧
        (A = 0 ∨ B = 0 ∨
          (A.natDegree = 0 ∧ B.natDegree = 0) ∨
          A.natDegree + 2 * B.natDegree ≤
            max
              (firstIntegralOnePolynomial410
                0 0 0 0 0 0 0 A B C0).natDegree
              (gammaLaterOneRest410
                delta zeta eta theta A B C0).natDegree)) ∨
      (B.natDegree = 0 ∧
        (A ^ 2 - (4 : k) • C0).natDegree = 0) ∨
      B.natDegree + (A ^ 2 - (4 : k) • C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (gammaLaterTwoRest410 delta zeta eta theta A B C0).natDegree)) ∧
    GammaSecondCoreResidual410 delta zeta eta theta A B C0

theorem discriminantGammaNewtonResidual410_coordinate_refinement
    (delta zeta eta theta : k) (A B C0 : k[X])
    (hold : DiscriminantGammaNewtonResidual410
      delta zeta eta theta A B C0) :
    CoordinateGammaNewtonResidual410 delta zeta eta theta A B C0 := by
  have hsecond : GammaSecondCoreResidual410
      delta zeta eta theta A B C0 := hold.2
  refine ⟨?_, hsecond⟩
  rcases hold.1 with hB | hU | hconstant | hcompetition
  · exact Or.inl ⟨hB,
      gammaSecondCoreResidual410_zeroB_refinement
        delta zeta eta theta A B C0 hB hsecond⟩
  · exact Or.inr (Or.inl ⟨hU,
      gammaSecondCoreResidual410_zeroU_refinement
        delta zeta eta theta A B C0 hU hsecond⟩)
  · exact Or.inr (Or.inr (Or.inl hconstant))
  · exact Or.inr (Or.inr (Or.inr hcompetition))

/-! ## Constant, integrated, and normalized source wrappers -/

def GammaCoordinateNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      CoordinateGammaNewtonResidual410 delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaCoordinateNoncubic_earlyLoad_residual
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
      GammaCoordinateNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaDiscriminantNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      discriminantGammaNewtonResidual410_coordinate_refinement
        delta zeta eta theta A B C0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaCoordinateNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaCoordinateNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaCoordinateNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaCoordinateNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaCoordinateNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaCoordinateNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaCoordinateFan410

end Max11DegreeRoutes
