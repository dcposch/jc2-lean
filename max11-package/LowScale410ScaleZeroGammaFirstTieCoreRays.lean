import LowScale410ScaleZeroGammaFirstTieCoreDeletion

/-!
# Exact rays for the core-zero fixed-face tie

The two outer sectors left by the first tie deletion are not genuine sectors.
The high-`B` side is forced onto `4 deg B = 3 deg U`; the low-`B` side is
forced onto `3 deg B = deg U`, and requires `delta != 0`.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFirstTieCoreRays410

variable {k : Type*} [Field k] [CharZero k]

def gammaI1CoreZeroHighBRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (80 : k) • U ^ 3 + (-(320 * delta : k)) • (A ^ 2 * B) -
    (1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_coreZero_eq_B4_add_highRest
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(320 : k)) • B ^ 4 +
        gammaI1CoreZeroHighBRest410 gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOne410_coreZero_eq_U3_add_rest
    gamma delta zeta eta theta A B U hcore]
  simp only [gammaI1TieCoreZeroRest410, gammaI1CoreZeroHighBRest410]
  module

theorem gammaI1CoreZeroHighBRest410_natDegree_lt_B4
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hstrict : 3 * U.natDegree < 4 * B.natDegree) :
    (gammaI1CoreZeroHighBRest410
      gamma delta zeta eta theta A B U).natDegree < 4 * B.natDegree := by
  simp only [gammaI1CoreZeroHighBRest410]
  compute_degree
  omega

theorem constantDiscriminantI1_gamma_fixedTie_coreZero_highSector_ray
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0)
    (hhigh : 3 * U.natDegree ≤ 4 * B.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    4 * B.natDegree = 3 * U.natDegree := by
  have hA : A ≠ 0 := by
    intro hAzero
    have hUzero : U ^ 2 = 0 := by simpa [hAzero] using hcore
    exact hU (eq_zero_of_pow_eq_zero hUzero)
  by_contra hne
  have hstrict : 3 * U.natDegree < 4 * B.natDegree := by omega
  have hrest := gammaI1CoreZeroHighBRest410_natDegree_lt_B4
    gamma delta zeta eta theta A B U hA hB hU htie hstrict
  rw [discriminantInvariantOne410_coreZero_eq_B4_add_highRest
    gamma delta zeta eta theta A B U hcore] at hOne
  exact (smul_add_lower_ne_C410 (-(320 : k)) q (B ^ 4)
    (gammaI1CoreZeroHighBRest410 gamma delta zeta eta theta A B U)
    (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB)
    (by omega)
    (by rw [natDegree_pow]) hrest) hOne

private theorem gammaTie_natDegree_smul_lt (c : k) {p : k[X]} {L : ℕ}
    (hp : p.natDegree < L) : (c • p).natDegree < L :=
  (natDegree_smul_le c p).trans_lt hp

private theorem gammaTie_natDegree_add_lt {p q : k[X]} {L : ℕ}
    (hp : p.natDegree < L) (hq : q.natDegree < L) :
    (p + q).natDegree < L :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem gammaTie_natDegree_sub_lt {p q : k[X]} {L : ℕ}
    (hp : p.natDegree < L) (hq : q.natDegree < L) :
    (p - q).natDegree < L :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

theorem gammaI1TieCoreZeroRest410_deltaZero_natDegree_lt_U3
    (gamma zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hlow : 3 * B.natDegree ≤ U.natDegree)
    (hUpos : 0 < U.natDegree) :
    (gammaI1TieCoreZeroRest410
      gamma 0 zeta eta theta A B U).natDegree < 3 * U.natDegree := by
  simp only [gammaI1TieCoreZeroRest410, zero_mul, mul_zero, zero_smul,
    neg_zero, zero_add, zero_sub, add_zero, sub_zero]
  have hAB2 : ((1536 * gamma : k) • (A * B ^ 2)).natDegree <
      3 * U.natDegree := by
    apply gammaTie_natDegree_smul_lt
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hAB : ((1536 * zeta : k) • (A * B)).natDegree <
      3 * U.natDegree := by
    apply gammaTie_natDegree_smul_lt
    rw [natDegree_mul hA hB]
    omega
  have hB4 : ((320 : k) • B ^ 4).natDegree < 3 * U.natDegree := by
    apply gammaTie_natDegree_smul_lt
    rw [natDegree_pow]
    omega
  have hBterm : ((2048 * theta : k) • B).natDegree <
      3 * U.natDegree := by
    apply gammaTie_natDegree_smul_lt
    omega
  have hU2 : ((192 * gamma : k) • U ^ 2).natDegree <
      3 * U.natDegree := by
    apply gammaTie_natDegree_smul_lt
    rw [natDegree_pow]
    omega
  have hUterm : ((1024 * eta : k) • U).natDegree <
      3 * U.natDegree := by
    apply gammaTie_natDegree_smul_lt
    omega
  apply gammaTie_natDegree_sub_lt
  · apply gammaTie_natDegree_add_lt
    · apply gammaTie_natDegree_add_lt
      · apply gammaTie_natDegree_sub_lt
        · apply gammaTie_natDegree_sub_lt
          · simpa only [natDegree_neg] using hAB2
          · exact hAB
        · exact hB4
      · exact hBterm
    · exact hU2
  · exact hUterm

def gammaI1CoreZeroLowDeltaRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (80 : k) • U ^ 3 - (1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (320 : k) • B ^ 4 -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_coreZero_eq_deltaA2B_add_lowRest
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(320 * delta : k)) • (A ^ 2 * B) +
        gammaI1CoreZeroLowDeltaRest410 gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOne410_coreZero_eq_U3_add_rest
    gamma delta zeta eta theta A B U hcore]
  simp only [gammaI1TieCoreZeroRest410, gammaI1CoreZeroLowDeltaRest410]
  module

theorem gammaI1CoreZeroLowDeltaRest410_natDegree_lt_deltaA2B
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hstrict : 3 * B.natDegree < U.natDegree) :
    (gammaI1CoreZeroLowDeltaRest410
      gamma delta zeta eta theta A B U).natDegree <
        2 * A.natDegree + B.natDegree := by
  simp only [gammaI1CoreZeroLowDeltaRest410]
  compute_degree
  omega

theorem constantDiscriminantI1_gamma_fixedTie_coreZero_lowSector_ray
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0)
    (hlow : 3 * B.natDegree ≤ U.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree := by
  have hA : A ≠ 0 := by
    intro hAzero
    have hUzero : U ^ 2 = 0 := by simpa [hAzero] using hcore
    exact hU (eq_zero_of_pow_eq_zero hUzero)
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  have hdelta : delta ≠ 0 := by
    intro hdeltaZero
    subst delta
    have hrest := gammaI1TieCoreZeroRest410_deltaZero_natDegree_lt_U3
      gamma zeta eta theta A B U hA hB hU htie hlow hUpos
    rw [discriminantInvariantOne410_coreZero_eq_U3_add_rest
      gamma 0 zeta eta theta A B U hcore] at hOne
    exact (smul_add_lower_ne_C410 (80 : k) q (U ^ 3)
      (gammaI1TieCoreZeroRest410 gamma 0 zeta eta theta A B U)
      (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hU) (by omega)
      (by rw [natDegree_pow]) hrest) hOne
  refine ⟨hdelta, ?_⟩
  by_contra hne
  have hstrict : 3 * B.natDegree < U.natDegree := by omega
  have hrest := gammaI1CoreZeroLowDeltaRest410_natDegree_lt_deltaA2B
    gamma delta zeta eta theta A B U hA hB hU htie hstrict
  rw [discriminantInvariantOne410_coreZero_eq_deltaA2B_add_lowRest
    gamma delta zeta eta theta A B U hcore] at hOne
  have hmain : (A ^ 2 * B).natDegree =
      2 * A.natDegree + B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
  exact (smul_add_lower_ne_C410 (-(320 * delta : k)) q (A ^ 2 * B)
    (gammaI1CoreZeroLowDeltaRest410 gamma delta zeta eta theta A B U)
    (2 * A.natDegree + B.natDegree)
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
    (mul_ne_zero (pow_ne_zero 2 hA) hB)
    (by omega) hmain hrest) hOne

theorem constantDiscriminantI1_gamma_fixedTie_coreZero_exactRays
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    4 * B.natDegree = 3 * U.natDegree ∨
      (delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree) := by
  rcases constantDiscriminantI1_gamma_fixedTie_coreZero_outerSectors
      gamma delta zeta eta theta q A B U hB hU hendpoint htie hcore hOne with
    hhigh | hlow
  · exact Or.inl (constantDiscriminantI1_gamma_fixedTie_coreZero_highSector_ray
      gamma delta zeta eta theta q A B U hB hU htie hcore hhigh hOne)
  · exact Or.inr (constantDiscriminantI1_gamma_fixedTie_coreZero_lowSector_ray
      gamma delta zeta eta theta q A B U hB hU hendpoint htie hcore hlow hOne)

def GammaI2ZeroFaceTieCoreRaysSelector410
    (delta : k) (L : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      (U ^ 2 - (8 : k) • (A * B ^ 2) ≠ 0 ∨
        4 * B.natDegree = 3 * U.natDegree ∨
        (delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree))) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceTieCoreRefinedSelector410_exactRays_refinement
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (L : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2ZeroFaceTieCoreRefinedSelector410 L A B U) :
    GammaI2ZeroFaceTieCoreRaysSelector410 delta L A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · right
    left
    refine ⟨htie.1, ?_⟩
    by_cases hcore : U ^ 2 - (8 : k) • (A * B ^ 2) = 0
    · right
      exact constantDiscriminantI1_gamma_fixedTie_coreZero_exactRays
        gamma delta zeta eta theta q A B U hB hU hendpoint htie.1 hcore hOne
    · exact Or.inl hcore
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionTieCoreRaysFan410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceTieCoreRaysSelector410 delta
      (gammaI2DeltaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceTieCoreRaysSelector410 delta
      (gammaI2ZetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceTieCoreRaysSelector410 delta
        (gammaI2ThetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceTieCoreRaysSelector410 delta
        (gammaI2BaseEnvelope410 B U) A B U)

theorem gammaI2FirstCompetitionTieCoreRefinedFan410_exactRays_refinement
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2FirstCompetitionTieCoreRefinedFan410
      delta zeta theta A B U) :
    GammaI2FirstCompetitionTieCoreRaysFan410 delta zeta theta A B U := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceTieCoreRefinedSelector410_exactRays_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2DeltaEnvelope410 A B U) hB hU hendpoint hOne hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceTieCoreRefinedSelector410_exactRays_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2ZetaEnvelope410 A B U) hB hU hendpoint hOne hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceTieCoreRefinedSelector410_exactRays_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2ThetaEnvelope410 A B U) hB hU hendpoint hOne
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceTieCoreRefinedSelector410_exactRays_refinement
        gamma delta zeta eta theta q A B U
          (gammaI2BaseEnvelope410 B U) hB hU hendpoint hOne
            hbase.2.2.2⟩))

def FirstTieCoreRaysGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FirstTieCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionTieCoreRaysFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)

theorem firstTieCoreDeletedGammaNewtonResidual410_exactRays_refinement
    (gamma delta zeta eta theta k1 : k) (A B C0 : k[X])
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hold : FirstTieCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FirstTieCoreRaysGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact gammaI2FirstCompetitionTieCoreRefinedFan410_exactRays_refinement
    gamma delta zeta eta theta (2048 * k1) A B U
      hold.1.1.1.2 hold.1.1.1.1.2 hold.1.1.2 hOneD hold.2

/-! ## Source-facing refinement -/

def GammaFirstTieCoreRaysNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FirstTieCoreRaysGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFirstTieCoreRaysNoncubic_residual
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
      GammaFirstTieCoreRaysNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaFirstTieCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      firstTieCoreDeletedGammaNewtonResidual410_exactRays_refinement
        gamma delta zeta eta theta k1 A B C0 hOne0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFirstTieCoreRaysNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaFirstTieCoreRaysNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFirstTieCoreRaysNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFirstTieCoreRaysNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaFirstTieCoreRaysNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaFirstTieCoreRaysNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFirstTieCoreRays410

end Max11DegreeRoutes
