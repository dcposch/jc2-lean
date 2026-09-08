import LowScale410ScaleZeroPositiveNoncubicBeta

/-!
# Eliminating the constant-`B` dropped-discriminant beta wall

On the sharp residual

`deg B = 0`, `deg C0 = 2 deg A`, `lc(A)^2 = 4 lc(C0)`,

the discriminant `U = A^2 - 4 C0` has degree strictly below `2 deg A`.
In the discriminant `I2` numerator the beta monomial `140 beta A^4` is then
the unique top face.  This excludes the entire constant-`B` beta branch,
with arbitrary later loads.  Consequently every genuine noncubic beta
survivor has positive `deg B`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section ConstantBDropElimination410

variable {k : Type*} [Field k] [CharZero k]

theorem discriminant_natDegree_lt_of_balanced_leading_drop
    (A C0 : k[X]) (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hdrop : A.leadingCoeff ^ 2 = 4 * C0.leadingCoeff) :
    (A ^ 2 - (4 : k) • C0).natDegree < 2 * A.natDegree := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  change U.natDegree < 2 * A.natDegree
  have hUle : U.natDegree ≤ 2 * A.natDegree := by
    dsimp only [U]
    exact (natDegree_sub_le _ _).trans <| max_le
      (by rw [natDegree_pow])
      (by rw [natDegree_smul C0 (by norm_num : (4 : k) ≠ 0), hbalanced])
  have hUcoeff : U.coeff (2 * A.natDegree) = 0 := by
    dsimp only [U]
    have hA : A ≠ 0 := by
      intro hzero
      rw [hzero, natDegree_zero] at hApos
      omega
    have hC0 : C0 ≠ 0 := by
      intro hzero
      rw [hzero, natDegree_zero] at hbalanced
      omega
    have hA2deg : (A ^ 2).natDegree = 2 * A.natDegree := by
      rw [natDegree_pow]
    have hA2coeff : (A ^ 2).coeff (2 * A.natDegree) =
        A.leadingCoeff ^ 2 := by
      rw [← hA2deg, coeff_natDegree, leadingCoeff_pow]
    have h4Ccoeff : ((4 : k) • C0).coeff (2 * A.natDegree) =
        4 * C0.leadingCoeff := by
      rw [coeff_smul, smul_eq_mul, ← hbalanced, coeff_natDegree]
    rw [coeff_sub, hA2coeff, h4Ccoeff, hdrop, sub_self]
  by_contra hnot
  have hUdeg : U.natDegree = 2 * A.natDegree := by omega
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUdeg
    omega
  rw [← hUdeg, coeff_natDegree] at hUcoeff
  exact (leadingCoeff_ne_zero.mpr hU) hUcoeff

/-- Every term of the scale-zero discriminant `I2` numerator except the
distinguished beta face `A^4`. -/
def constantBDropTwoRest410
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 - (336 * beta : k) • (A ^ 2 * U) +
    (768 * zeta : k) • A ^ 2 - (1280 : k) • (A * B ^ 3) -
    (1344 * beta : k) • (A * B ^ 2) - (640 * delta : k) • (A * U) +
    (2048 * theta : k) • A + (1280 * delta : k) • B ^ 2 +
    (480 : k) • (B * U ^ 2) - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B + (336 * beta : k) • U ^ 2 -
    (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_eq_constantBDrop_face_add_rest
    (beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 beta gamma delta zeta eta theta A B U =
      (140 * beta : k) • A ^ 4 +
        constantBDropTwoRest410 beta gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantTwoNumerator410, constantBDropTwoRest410]
  abel

theorem constantBDropTwoRest410_natDegree_lt
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hApos : 0 < A.natDegree) (hB0 : B.natDegree = 0)
    (hUlow : U.natDegree < 2 * A.natDegree) :
    (constantBDropTwoRest410
      beta gamma delta zeta eta theta A B U).natDegree <
        4 * A.natDegree := by
  simp only [constantBDropTwoRest410]
  compute_degree
  omega

/-- The exact constant-`B` dropped-discriminant wall is empty. -/
theorem positiveNoncubicBeta_constantB_drop_impossible
    (beta gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hbeta : beta ≠ 0) (hB0 : B.natDegree = 0)
    (hApos : 0 < A.natDegree)
    (hbalanced : C0.natDegree = 2 * A.natDegree)
    (hdrop : A.leadingCoeff ^ 2 = 4 * C0.leadingCoeff)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hUlow : U.natDegree < 2 * A.natDegree := by
    simpa only [U] using
      (discriminant_natDegree_lt_of_balanced_leading_drop
        A C0 hApos hbalanced hdrop)
  have hrest := constantBDropTwoRest410_natDegree_lt
    beta gamma delta zeta eta theta A B U hApos hB0 hUlow
  have hfaceDeg : (A ^ 4).natDegree = 4 * A.natDegree := by
    rw [natDegree_pow]
  have hTwoD :
      discriminantInvariantTwoNumerator410
          0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have heq :
      (140 * beta : k) • A ^ 4 +
          constantBDropTwoRest410
            beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    rw [← discriminantInvariantTwo410_eq_constantBDrop_face_add_rest]
    exact hTwoD
  exact (smul_add_lower_ne_C410 (140 * beta : k) (2048 * k2) (A ^ 4)
    (constantBDropTwoRest410 beta gamma delta zeta eta theta A B U)
    (4 * A.natDegree) (mul_ne_zero (by norm_num) hbeta)
    (pow_ne_zero 4 hA) (by omega) hfaceDeg hrest) heq

/-! ## Smaller beta packet and source transport -/

def PositiveBNoncubicBetaNewtonResidual410
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
      0 < B.natDegree

def PositiveBNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      PositiveBNoncubicBetaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_positiveBNoncubic_earlyLoad_residual
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
      PositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_droppedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · rcases hbeta.2.2.2.2.2.2 with hBpos | hdrop
    · left
      exact ⟨hbeta.1, hbeta.2.1, hbeta.2.2.1, hbeta.2.2.2.1,
        hbeta.2.2.2.2.1, hbeta.2.2.2.2.2.1, hBpos⟩
    · have hTwo0 : firstIntegralTwoPolynomial410
          0 beta gamma delta zeta eta theta A B C0 = C k2 := by
        simpa [hold.1] using hTwo
      exact (positiveNoncubicBeta_constantB_drop_impossible
        beta gamma delta zeta eta theta k2 A B C0 hbeta.1 hdrop.1
          hdrop.2.1 hdrop.2.2.1 hdrop.2.2.2 hTwo0).elim
  · exact Or.inr hlater

theorem integrated410_positiveBNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      PositiveBNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_positiveBNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_positiveBNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          PositiveBNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_positiveBNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end ConstantBDropElimination410

end Max11DegreeRoutes
