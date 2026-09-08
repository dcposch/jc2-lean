import LowScale410ScaleZeroGammaUZeroRaysElimination

/-!
# Deletion of the coordinate-degree boundaries on `U=0`

If `deg A=0<deg B`, the `B^4` face of the second invariant is unique.  If
`deg B=0<deg A`, a nonzero delta gives the unique `A^2 B` face.  For
`delta=0`, constancy of the second invariant forces
`gamma lc(B)+zeta=0`; hence `zeta≠0`, and the first invariant has the
unique quadratic face `zeta A^2`.  This closes `U=0` completely.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section GammaUZeroBoundaryElimination410

variable {k : Type*} [Field k] [CharZero k]

theorem firstIntegralTwo410_discriminantZero_specialization
    (gamma delta zeta eta theta : k) (A B : k[X]) :
    firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) =
      (5 / 32 * delta : k) • A ^ 3 +
        (3 / 8 * zeta : k) • A ^ 2 -
        (5 / 8 : k) • (A * B ^ 3) + theta • A +
        (5 / 8 * delta : k) • B ^ 2 + (2 * eta : k) • B := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [firstIntegralTwoPolynomial410, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_zero,
    map_mul]
  ring

theorem gamma_U_zero_A_degree_zero_boundary_impossible
    (gamma delta zeta eta theta k1 : k) (A B : k[X])
    (hA0 : A.natDegree = 0) (hBpos : 0 < B.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k1) :
    False := by
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hspecial := hOne
  rw [firstIntegralOne410_discriminantZero_specialization] at hspecial
  let R : k[X] :=
    -(3 / 4 * gamma : k) • (A * B ^ 2) -
      (5 / 32 * delta : k) • (A ^ 2 * B) +
      gammaUZeroLowerRestOne410 zeta theta A B
  have heq : (-(5 / 32 : k)) • B ^ 4 + R = C k1 := by
    simpa [R, sub_eq_add_neg, add_assoc] using hspecial
  have hrest : R.natDegree < 4 * B.natDegree := by
    dsimp only [R]
    simp only [gammaUZeroLowerRestOne410]
    compute_degree
    omega
  exact (smul_add_lower_ne_C410 (-(5 / 32 : k)) k1 (B ^ 4) R
    (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB) (by omega)
    (by rw [natDegree_pow]) hrest) heq

theorem gamma_U_zero_B_degree_zero_boundary_impossible
    (gamma delta zeta eta theta k2 k1 : k) (A B : k[X])
    (hgamma : gamma ≠ 0) (hApos : 0 < A.natDegree)
    (hB0 : B.natDegree = 0) (hB : B ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B ((1 / 4 : k) • A ^ 2) = C k1) :
    False := by
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hOneSpecial := hOne
  rw [firstIntegralOne410_discriminantZero_specialization] at hOneSpecial
  by_cases hdelta : delta = 0
  · let M : k[X] :=
        -(3 / 4 * gamma : k) • (A * B ^ 2) -
          (3 / 4 * zeta : k) • (A * B)
    let R : k[X] := (-(5 / 32 : k)) • B ^ 4 + theta • B
    have heq : M + R = C k1 := by
      simpa [M, R, gammaUZeroLowerRestOne410, hdelta,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hOneSpecial
    have hRdegree : R.natDegree < A.natDegree := by
      dsimp only [R]
      compute_degree
      omega
    have hAB2deg : (A * B ^ 2).natDegree = A.natDegree := by
      rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow, hB0]
      omega
    have hABdeg : (A * B).natDegree = A.natDegree := by
      rw [natDegree_mul hA hB, hB0]
      omega
    have hcoeff := congrArg
      (fun P : k[X] => P.coeff A.natDegree) heq
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hRdegree, add_zero,
      show (C k1 : k[X]).coeff A.natDegree = 0 by
        apply coeff_eq_zero_of_natDegree_lt
        rw [natDegree_C]
        omega] at hcoeff
    dsimp only [M] at hcoeff
    rw [coeff_sub, coeff_smul, coeff_smul,
      show (A * B ^ 2).coeff A.natDegree =
          A.leadingCoeff * B.leadingCoeff ^ 2 by
        rw [← hAB2deg, coeff_natDegree, leadingCoeff_mul,
          leadingCoeff_pow],
      show (A * B).coeff A.natDegree =
          A.leadingCoeff * B.leadingCoeff by
        rw [← hABdeg, coeff_natDegree, leadingCoeff_mul]] at hcoeff
    simp only [smul_eq_mul] at hcoeff
    have hwall : gamma * B.leadingCoeff + zeta = 0 := by
      apply (mul_left_cancel₀ (mul_ne_zero hAlc hBlc))
      linear_combination (-4 / 3 : k) * hcoeff
    have hzeta : zeta ≠ 0 := by
      intro hzeta
      rw [hzeta, add_zero] at hwall
      exact (mul_ne_zero hgamma hBlc) hwall
    have hTwoSpecial := hTwo
    rw [firstIntegralTwo410_discriminantZero_specialization] at hTwoSpecial
    let R2 : k[X] :=
      -(5 / 8 : k) • (A * B ^ 3) + theta • A +
        (2 * eta : k) • B
    have heq2 : (3 / 8 * zeta : k) • A ^ 2 + R2 = C k2 := by
      simpa [R2, hdelta, sub_eq_add_neg, add_assoc] using hTwoSpecial
    have hR2degree : R2.natDegree < 2 * A.natDegree := by
      dsimp only [R2]
      compute_degree
      omega
    exact (smul_add_lower_ne_C410 (3 / 8 * zeta : k) k2 (A ^ 2) R2
      (2 * A.natDegree) (mul_ne_zero (by norm_num) hzeta)
      (pow_ne_zero 2 hA) (by omega) (by rw [natDegree_pow])
      hR2degree) heq2
  · let R : k[X] :=
        (-(5 / 32 : k)) • B ^ 4 -
          (3 / 4 * gamma : k) • (A * B ^ 2) +
          gammaUZeroLowerRestOne410 zeta theta A B
    have heq : (-(5 / 32 * delta : k)) • (A ^ 2 * B) + R = C k1 := by
      simpa [R, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hOneSpecial
    have hrest : R.natDegree < 2 * A.natDegree := by
      dsimp only [R]
      simp only [gammaUZeroLowerRestOne410]
      compute_degree
      omega
    have hmain : (A ^ 2 * B).natDegree = 2 * A.natDegree := by
      rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow, hB0]
      omega
    exact (smul_add_lower_ne_C410 (-(5 / 32 * delta : k)) k1
      (A ^ 2 * B) R (2 * A.natDegree)
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
      (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hmain hrest) heq

def UZeroDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  UZeroRaysDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    A ^ 2 - (4 : k) • C0 ≠ 0

theorem UZeroRaysDeletedGammaNewtonResidual410_boundary_refinement
    (gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hgamma : gamma ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hold : UZeroRaysDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    UZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  intro hU
  have hAC : A ^ 2 = (4 : k) • C0 := sub_eq_zero.mp hU
  have hC0 : C0 = (1 / 4 : k) • A ^ 2 := by
    calc
      C0 = (1 / 4 : k) • ((4 : k) • C0) := by module
      _ = (1 / 4 : k) • A ^ 2 := by rw [← hAC]
  rw [hC0] at hTwo hOne
  rcases UZeroRaysDeletedGammaNewtonResidual410_zeroU_selector
      gamma delta zeta eta theta A B C0 hU hold with hA0 | hB0
  · have hBpos : 0 < B.natDegree := by
      by_contra hnot
      exact hold.1.1.1.1.2 ⟨hU, hA0, by omega⟩
    exact gamma_U_zero_A_degree_zero_boundary_impossible
      gamma delta zeta eta theta k1 A B hA0 hBpos hOne
  · have hApos : 0 < A.natDegree := by
      by_contra hnot
      exact hold.1.1.1.1.2 ⟨hU, by omega, hB0⟩
    have hB : B ≠ 0 := by
      intro hBzero
      exact hold.1.1.2 ⟨hU, hBzero⟩
    exact gamma_U_zero_B_degree_zero_boundary_impossible
      gamma delta zeta eta theta k2 k1 A B hgamma hApos hB0 hB hTwo hOne

/-! ## Source-facing complete `U=0` deletion -/

def GammaUZeroDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      UZeroDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaUZeroDeletedNoncubic_earlyLoad_residual
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
      GammaUZeroDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaUZeroRaysDeletedNoncubic_earlyLoad_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      UZeroRaysDeletedGammaNewtonResidual410_boundary_refinement
        gamma delta zeta eta theta k2 k1 A B C0 hgamma.2.1
          hTwo0 hOne0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaUZeroDeletedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaUZeroDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaUZeroDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaUZeroDeletedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaUZeroDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaUZeroDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaUZeroBoundaryElimination410

end Max11DegreeRoutes
