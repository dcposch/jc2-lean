import LowScale410ScaleZeroGammaFirstCompetitionFan

/-!
# Deletion of the middle sector of the first-face tie

On the fixed-face tie `deg(A B^3) = deg(B U^2)`, one has
`deg A + 2 deg B = 2 deg U`.  If the second gamma core also vanishes,
`U^2 = 8 A B^2`, the tied principal part of the first invariant becomes
the nonzero term `80 U^3`.  It can be balanced only in the two outer
degree sectors `3 deg U <= 4 deg B` or `3 deg B <= deg U`.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFirstTieCoreDeletion410

variable {k : Type*} [Field k] [CharZero k]

def gammaI1TieCoreZeroRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(320 * delta : k)) • (A ^ 2 * B) -
    (1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (320 : k) • B ^ 4 -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_coreZero_eq_U3_add_rest
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (80 : k) • U ^ 3 +
        gammaI1TieCoreZeroRest410 gamma delta zeta eta theta A B U := by
  have hU2 : U ^ 2 = (8 : k) • (A * B ^ 2) := sub_eq_zero.mp hcore
  have hAB2 : A * B ^ 2 = (1 / 8 : k) • U ^ 2 := by
    calc
      A * B ^ 2 = (1 / 8 : k) • ((8 : k) • (A * B ^ 2)) := by module
      _ = (1 / 8 : k) • U ^ 2 := by rw [← hU2]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantOneNumerator410,
    gammaI1TieCoreZeroRest410, hAB2, Polynomial.smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

theorem gammaI1TieCoreZeroRest410_natDegree_lt_U3
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hupper : ¬ 3 * U.natDegree ≤ 4 * B.natDegree)
    (hlower : ¬ 3 * B.natDegree ≤ U.natDegree) :
    (gammaI1TieCoreZeroRest410
      gamma delta zeta eta theta A B U).natDegree < 3 * U.natDegree := by
  simp only [gammaI1TieCoreZeroRest410]
  compute_degree
  omega

/-- The core-zero fixed-face tie has no points in the open middle sector
`deg U / 3 < deg B < 3 deg U / 4`. -/
theorem constantDiscriminantI1_gamma_fixedTie_coreZero_outerSectors
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    3 * U.natDegree ≤ 4 * B.natDegree ∨
      3 * B.natDegree ≤ U.natDegree := by
  have hA : A ≠ 0 := by
    intro hAzero
    have hUzero : U ^ 2 = 0 := by
      simpa [hAzero] using hcore
    exact hU (eq_zero_of_pow_eq_zero hUzero)
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  by_contra hsectors
  push_neg at hsectors
  have hrest := gammaI1TieCoreZeroRest410_natDegree_lt_U3
    gamma delta zeta eta theta A B U hA hB hU htie
      (by omega) (by omega)
  rw [discriminantInvariantOne410_coreZero_eq_U3_add_rest
    gamma delta zeta eta theta A B U hcore] at hOne
  exact (smul_add_lower_ne_C410 (80 : k) q (U ^ 3)
    (gammaI1TieCoreZeroRest410 gamma delta zeta eta theta A B U)
    (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hU) (by omega)
    (by rw [natDegree_pow]) hrest) hOne

def GammaI2ZeroFaceTieCoreRefinedSelector410
    (L : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      (U ^ 2 - (8 : k) • (A * B ^ 2) ≠ 0 ∨
        3 * U.natDegree ≤ 4 * B.natDegree ∨
        3 * B.natDegree ≤ U.natDegree)) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceSelector410_tieCore_refinement
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (L : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2ZeroFaceSelector410 L A B U) :
    GammaI2ZeroFaceTieCoreRefinedSelector410 L A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · right
    left
    refine ⟨htie, ?_⟩
    by_cases hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0
    · right
      exact constantDiscriminantI1_gamma_fixedTie_coreZero_outerSectors
        gamma delta zeta eta theta q A B U hB hU hendpoint htie hcore hOne
    · exact Or.inl hcore
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionTieCoreRefinedFan410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  (delta ≠ 0 ∧
      GammaI2ZeroFaceTieCoreRefinedSelector410
        (gammaI2DeltaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧
      GammaI2ZeroFaceTieCoreRefinedSelector410
        (gammaI2ZetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceTieCoreRefinedSelector410
        (gammaI2ThetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceTieCoreRefinedSelector410
        (gammaI2BaseEnvelope410 B U) A B U)

theorem gammaI2FirstCompetitionFan410_tieCore_refinement
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2FirstCompetitionFan410 delta zeta theta A B U) :
    GammaI2FirstCompetitionTieCoreRefinedFan410 delta zeta theta A B U := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceSelector410_tieCore_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2DeltaEnvelope410 A B U) hB hU hendpoint hOne hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceSelector410_tieCore_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2ZetaEnvelope410 A B U) hB hU hendpoint hOne hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceSelector410_tieCore_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2ThetaEnvelope410 A B U) hB hU hendpoint hOne
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceSelector410_tieCore_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2BaseEnvelope410 B U) hB hU hendpoint hOne
            hbase.2.2.2⟩))

def FirstTieCoreDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FirstCompetitionFanRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionTieCoreRefinedFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)

theorem firstCompetitionFanRefinedGammaNewtonResidual410_tieCore_refinement
    (gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hold : FirstCompetitionFanRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FirstTieCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact gammaI2FirstCompetitionFan410_tieCore_refinement
    gamma delta zeta eta theta (2048 * k1) A B U
      hold.1.1.2 hold.1.1.1.2 hold.1.2 hOneD hold.2

/-! ## Source-facing refinement -/

def GammaFirstTieCoreDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FirstTieCoreDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFirstTieCoreDeletedNoncubic_residual
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
      GammaFirstTieCoreDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaFirstCompetitionFanNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      firstCompetitionFanRefinedGammaNewtonResidual410_tieCore_refinement
        gamma delta zeta eta theta k1 A B C0 hOne0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFirstTieCoreDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaFirstTieCoreDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFirstTieCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFirstTieCoreDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaFirstTieCoreDeletedNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaFirstTieCoreDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFirstTieCoreDeletion410

end Max11DegreeRoutes
