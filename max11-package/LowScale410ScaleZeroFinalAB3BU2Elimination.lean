import LowScale410ScaleZeroA4BU2Tie

/-!
# Eliminating the final positive-beta wall

The final geometry is `a≤b`, `2u=a+2b`.  If `a=b`, it is the already
deleted triple point.  For `a<b`, split at `3a=2b`:

* below the boundary, `B^4` is uniquely leading in `I1`;
* above it, the `AB^3/BU^2` face of `I2` and the `AB^2U/U^3` face of `I1`
  give incompatible leading-coefficient equations;
* on the boundary, the degrees are `(2n,3n,4n)`, and the canonical aligned
  terminal theorem applies.

This deletes the whole positive-beta branch with arbitrary later loads.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section FinalAB3BU2Elimination410

variable {k : Type*} [Field k] [CharZero k]

theorem scaleZeroB4RestOne410_natDegree_lt_on_final_low
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree)
    (hplane : 2 * U.natDegree = A.natDegree + 2 * B.natDegree)
    (hlow : 3 * A.natDegree < 2 * B.natDegree) :
    (lWallFanRestOneB4_410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        4 * B.natDegree := by
  simp only [lWallFanRestOneB4_410, lWallLowURestOne410, mul_zero,
    neg_zero, zero_smul, zero_add, add_zero]
  compute_degree
  omega

theorem scaleZero_positiveBeta_final_low_impossible
    (beta gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree)
    (hplane : 2 * (A ^ 2 - (4 : k) • C0).natDegree =
      A.natDegree + 2 * B.natDegree)
    (hlow : 3 * A.natDegree < 2 * B.natDegree)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hrest := scaleZeroB4RestOne410_natDegree_lt_on_final_low
    beta gamma delta zeta eta theta A B U hBpos
      (by simpa only [U] using hplane) hlow
  have hOneD : discriminantInvariantOneNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [discriminantInvariantOneNumerator410_eq_fanB4_add_rest] at hOneD
  exact (smul_add_lower_ne_C410 (-(320 : k)) (2048 * k1) (B ^ 4)
    (lWallFanRestOneB4_410 0 beta gamma delta zeta eta theta A B U)
    (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB) (by omega)
    (by rw [natDegree_pow]) hrest) hOneD

theorem scaleZeroIntermediateRestTwo410_natDegree_lt_on_final_high
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree) (hAltB : A.natDegree < B.natDegree)
    (hplane : 2 * U.natDegree = A.natDegree + 2 * B.natDegree)
    (hhigh : 2 * B.natDegree < 3 * A.natDegree) :
    (lWallIntermediateRestTwo410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        A.natDegree + 3 * B.natDegree := by
  simp only [lWallIntermediateRestTwo410, mul_zero, neg_zero, zero_smul,
    zero_add, add_zero]
  compute_degree
  omega

theorem scaleZeroIntermediateRestOne410_natDegree_lt_on_final_high
    (beta gamma delta zeta eta theta : k) (A B U : k[X])
    (hBpos : 0 < B.natDegree) (hAltB : A.natDegree < B.natDegree)
    (hplane : 2 * U.natDegree = A.natDegree + 2 * B.natDegree)
    (hhigh : 2 * B.natDegree < 3 * A.natDegree) :
    (lWallIntermediateRestOne410
      0 beta gamma delta zeta eta theta A B U).natDegree <
        3 * U.natDegree := by
  simp only [lWallIntermediateRestOne410, mul_zero, neg_zero, zero_smul,
    zero_add, add_zero]
  compute_degree
  omega

theorem scaleZero_positiveBeta_final_high_impossible
    (beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hBpos : 0 < B.natDegree) (hAltB : A.natDegree < B.natDegree)
    (hplane : 2 * (A ^ 2 - (4 : k) • C0).natDegree =
      A.natDegree + 2 * B.natDegree)
    (hhigh : 2 * B.natDegree < 3 * A.natDegree)
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1) : False := by
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hApos : 0 < A.natDegree := by omega
  have hUplane : 2 * U.natDegree =
      A.natDegree + 2 * B.natDegree := by simpa only [U] using hplane
  have hUpos : 0 < U.natDegree := by omega
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hApos
    omega
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hBpos
    omega
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hUpos
    omega
  have hrestTwo := scaleZeroIntermediateRestTwo410_natDegree_lt_on_final_high
    beta gamma delta zeta eta theta A B U hBpos hAltB hUplane hhigh
  have hrestOne := scaleZeroIntermediateRestOne410_natDegree_lt_on_final_high
    beta gamma delta zeta eta theta A B U hBpos hAltB hUplane hhigh
  have hTwoD : discriminantInvariantTwoNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD : discriminantInvariantOneNumerator410
      0 beta gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  rw [discriminantInvariantTwoNumerator410_eq_intermediateFace_add_rest] at hTwoD
  rw [discriminantInvariantOneNumerator410_eq_intermediateFace_add_rest] at hOneD
  have hAB3deg : (A * B ^ 3).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hBU2deg : (B * U ^ 2).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * U.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * U.natDegree := by
    rw [natDegree_pow]
  have hTwoCoeff := congrArg
    (fun P : k[X] => P.coeff (A.natDegree + 3 * B.natDegree)) hTwoD
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 3).coeff (A.natDegree + 3 * B.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff (A.natDegree + 3 * B.natDegree) =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hrestTwo, add_zero,
    show (C (2048 * k2) : k[X]).coeff
        (A.natDegree + 3 * B.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg
    (fun P : k[X] => P.coeff (3 * U.natDegree)) hOneD
  rw [coeff_add, coeff_sub, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff (3 * U.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow],
    show (U ^ 3).coeff (3 * U.natDegree) = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hrestOne, add_zero,
    show (C (2048 * k1) : k[X]).coeff (3 * U.natDegree) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hfaceTwo : (3 : k) * U.leadingCoeff ^ 2 =
      8 * A.leadingCoeff * B.leadingCoeff ^ 2 := by
    apply (mul_left_cancel₀ hBlc)
    linear_combination (1 / 160 : k) * hTwoCoeff
  have hfaceOne : (24 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 =
      U.leadingCoeff ^ 2 := by
    apply (mul_right_cancel₀ hUlc)
    linear_combination (1 / 40 : k) * hOneCoeff
  have hzero : (64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 = 0 := by
    linear_combination 3 * hfaceOne + hfaceTwo
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hAlc)
    (pow_ne_zero 2 hBlc)) hzero

/-- The final degree wall is empty in all three chambers. -/
theorem scaleZero_positiveBeta_final_AB3BU2_impossible
    (alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal : k)
    (A B C0 : k[X]) (hbeta : beta ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hfinal : FinalAB3BU2Tie410 A B (A ^ 2 - (4 : k) • C0))
    (hTwo : firstIntegralTwoPolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      0 beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hAleB := hfinal.1
  have hplane := hfinal.2
  by_cases hAB : A.natDegree = B.natDegree
  · have hFirst : 4 * A.natDegree =
        A.natDegree + 3 * B.natDegree := by omega
    have hUtop : 2 * (A ^ 2 - (4 : k) • C0).natDegree =
        3 * A.natDegree := by omega
    exact scaleZero_positiveBeta_A4AB3_highU_terminal_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
        A B C0 hbeta hBpos hFirst hUtop hTwo hLower
  · have hAltB : A.natDegree < B.natDegree := by omega
    by_cases hlow : 3 * A.natDegree < 2 * B.natDegree
    · exact scaleZero_positiveBeta_final_low_impossible
        beta gamma delta zeta eta theta k1 A B C0 hBpos hplane hlow hOne
    by_cases hboundary : 3 * A.natDegree = 2 * B.natDegree
    · have hdiv : 2 ∣ A.natDegree := by
        apply (by decide : Nat.Coprime 2 3).dvd_of_dvd_mul_right
        use B.natDegree
        omega
      obtain ⟨n, hnA⟩ := hdiv
      have hAdeg : A.natDegree = 2 * n := by omega
      have hBdeg : B.natDegree = 3 * n := by omega
      have hUdeg : (A ^ 2 - (4 : k) • C0).natDegree = 4 * n := by omega
      have hn : 0 < n := by omega
      have hA : A ≠ 0 := by
        intro hzero
        rw [hzero, natDegree_zero] at hAdeg
        omega
      have hB : B ≠ 0 := by
        intro hzero
        rw [hzero, natDegree_zero] at hBpos
        omega
      exact lWall410_aligned_original_terminal_impossible
        0 alpha beta gamma delta epsilon zeta eta theta iota k2 terminal
          A B C0 n hn hA hB hAdeg hBdeg hUdeg hTwo hLower
    · have hhigh : 2 * B.natDegree < 3 * A.natDegree := by omega
      exact scaleZero_positiveBeta_final_high_impossible
        beta gamma delta zeta eta theta k2 k1 A B C0 hBpos hAltB
          hplane hhigh hTwo hOne

/-! ## Source-facing deletion of beta -/

def BetaDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_betaDeletedNoncubic_earlyLoad_residual
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
      BetaDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta := by
  have hold := constantIntegral410_finalTiePositiveB_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · rcases hbeta with ⟨hbeta, hB, hfan, hfinal⟩
    have hTwo0 : firstIntegralTwoPolynomial410
        0 beta gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1] using hTwo
    have hOne0 : firstIntegralOnePolynomial410
        0 beta gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1] using hOne
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410
          0 alpha beta gamma delta epsilon zeta theta A B C0)
        (integratedZPolynomial410
          0 alpha beta gamma delta epsilon zeta eta iota A B C0)
        B C0 = C terminal := by
      simpa [hold.1] using hLower
    exact (scaleZero_positiveBeta_final_AB3BU2_impossible
      alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hbeta hfan.1.2.2.2.2 hfinal hTwo0 hOne0 hLower0).elim
  · exact hlater

theorem integrated410_betaDeletedNoncubic_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      BetaDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_betaDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_betaDeletedNoncubic_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          BetaDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_betaDeletedNoncubic_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end FinalAB3BU2Elimination410

end Max11DegreeRoutes
