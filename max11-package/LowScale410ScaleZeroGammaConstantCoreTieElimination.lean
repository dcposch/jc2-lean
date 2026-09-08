import LowScale410ScaleZeroGammaCoreNonzeroTiePacket

/-!
# Elimination for the constant nonzero core on the fixed-face tie

When `G = U^2 - 8 A B^2` is constant, the vanishing core top scalar makes
the principal first-invariant face `960 A B^2 U - 40 U^3` genuinely have
degree `3 deg U`.  Its Newton fan leaves only the two rays already exposed
in the core-zero calculation.  The second invariant deletes both rays.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaConstantCoreTieElimination410

variable {k : Type*} [Field k] [CharZero k]

def gammaConstantCorePrincipal410 (A B U : k[X]) : k[X] :=
  (960 : k) • (A * B ^ 2 * U) - (40 : k) • U ^ 3

def gammaConstantCoreLowRest410
    (delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(1536 * zeta : k)) • (A * B) -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B -
    (1024 * eta : k) • U

theorem discriminantInvariantOne410_constantCore_decomposition
    (gamma delta zeta eta theta c : k) (A B U : k[X])
    (hcoreC : gammaTieCore410 A B U = C c) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      gammaConstantCorePrincipal410 A B U - (320 : k) • B ^ 4 +
        (-(320 * delta : k)) • (A ^ 2 * B) +
        gammaConstantCoreLowRest410 delta zeta eta theta A B U +
        C (192 * gamma * c) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hcoreR := congrArg
    (algebraMap k[X] (RatFunc k)) hcoreC
  simp only [gammaTieCore410, gammaConstantCorePrincipal410,
    gammaConstantCoreLowRest410, discriminantInvariantOneNumerator410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C] at hcoreR ⊢
  simp only [map_ofNat] at hcoreR ⊢
  linear_combination (192 * RatFunc.C gamma : RatFunc k) * hcoreR

theorem gammaConstantCorePrincipal410_top_coeff
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (htop : gammaTieCoreTopScalar410 A B U = 0) :
    (gammaConstantCorePrincipal410 A B U).coeff (3 * U.natDegree) =
      (640 : k) * U.leadingCoeff * A.leadingCoeff * B.leadingCoeff ^ 2 := by
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * U.natDegree := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * U.natDegree := by
    rw [natDegree_pow]
  rw [gammaConstantCorePrincipal410, coeff_sub, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff (3 * U.natDegree) =
        (A.leadingCoeff * B.leadingCoeff ^ 2) * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul,
        leadingCoeff_mul, leadingCoeff_pow],
    show (U ^ 3).coeff (3 * U.natDegree) = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow]]
  simp only [smul_eq_mul, gammaTieCoreTopScalar410] at htop ⊢
  linear_combination (-40 * U.leadingCoeff) * htop

theorem gammaConstantCorePrincipal410_natDegree_eq
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (htop : gammaTieCoreTopScalar410 A B U = 0) :
    (gammaConstantCorePrincipal410 A B U).natDegree =
      3 * U.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simp only [gammaConstantCorePrincipal410]
    compute_degree
    omega
  · rw [gammaConstantCorePrincipal410_top_coeff A B U hA hB hU htie htop]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num)
        (leadingCoeff_ne_zero.mpr hU)) (leadingCoeff_ne_zero.mpr hA))
      (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hB))

theorem gammaConstantCoreLowRest410_natDegree_lt_threeU
    (delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hUpos : 0 < U.natDegree) :
    (gammaConstantCoreLowRest410 delta zeta eta theta A B U).natDegree <
      3 * U.natDegree := by
  simp only [gammaConstantCoreLowRest410]
  compute_degree
  omega

theorem constantDiscriminantI1_gamma_constantCore_tie_rays
    (gamma delta zeta eta theta q c : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcoreC : gammaTieCore410 A B U = C c)
    (htop : gammaTieCoreTopScalar410 A B U = 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    4 * B.natDegree = 3 * U.natDegree ∨
      (delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree) := by
  have hPdeg := gammaConstantCorePrincipal410_natDegree_eq
    A B U hA hB hU htie htop
  have hLow := gammaConstantCoreLowRest410_natDegree_lt_threeU
    delta zeta eta theta A B U hA hB hU htie hUpos
  have hdecomp := discriminantInvariantOne410_constantCore_decomposition
    gamma delta zeta eta theta c A B U hcoreC
  rw [hdecomp] at hOne
  let X0 : k[X] := gammaConstantCorePrincipal410 A B U -
      (320 : k) • B ^ 4 + (-(320 * delta : k)) • (A ^ 2 * B) +
      gammaConstantCoreLowRest410 delta zeta eta theta A B U
  have hfull : X0 + C (192 * gamma * c) = C q := by
    simpa only [X0] using hOne
  have heq : X0 = C (q - 192 * gamma * c) := by
    calc
      X0 = (X0 + C (192 * gamma * c)) - C (192 * gamma * c) := by
        module
      _ = C q - C (192 * gamma * c) := by rw [hfull]
      _ = C (q - 192 * gamma * c) := by rw [C_sub]
  by_cases hhigh : 4 * B.natDegree = 3 * U.natDegree
  · exact Or.inl hhigh
  by_cases hdelta : delta = 0
  · subst delta
    have hne : 4 * B.natDegree ≠ 3 * U.natDegree := hhigh
    rcases lt_or_gt_of_ne hne with hBbelow | hPbelow
    · let R : k[X] := (-(320 : k)) • B ^ 4 +
          gammaConstantCoreLowRest410 0 zeta eta theta A B U
      have hR : R.natDegree < 3 * U.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      have heqP : gammaConstantCorePrincipal410 A B U + R =
          C (q - 192 * gamma * c) := by
        dsimp only [X0, R] at heq ⊢
        simp only [mul_zero, neg_zero, zero_smul, add_zero] at heq ⊢
        rw [← heq]
        module
      exact False.elim ((smul_add_lower_ne_C410 (1 : k)
        (q - 192 * gamma * c) (gammaConstantCorePrincipal410 A B U) R
        (3 * U.natDegree) (by norm_num)
        (by intro hz; rw [hz, natDegree_zero] at hPdeg; omega)
        (by omega) hPdeg hR) (by simpa using heqP))
    · let R : k[X] := gammaConstantCorePrincipal410 A B U +
          gammaConstantCoreLowRest410 0 zeta eta theta A B U
      have hR : R.natDegree < 4 * B.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      have heqB : (-(320 : k)) • B ^ 4 + R =
          C (q - 192 * gamma * c) := by
        dsimp only [X0, R] at heq ⊢
        simp only [mul_zero, neg_zero, zero_smul, add_zero] at heq ⊢
        rw [← heq]
        module
      exact False.elim ((smul_add_lower_ne_C410 (-(320 : k))
        (q - 192 * gamma * c) (B ^ 4) R (4 * B.natDegree)
        (by norm_num) (pow_ne_zero 4 hB) (by omega)
        (by rw [natDegree_pow]) hR) heqB)
  · by_cases hlow : 3 * B.natDegree = U.natDegree
    · exact Or.inr ⟨hdelta, hlow⟩
    have hDne : 3 * U.natDegree ≠
        2 * A.natDegree + B.natDegree := by omega
    by_cases hBbelow : 4 * B.natDegree < 3 * U.natDegree
    · by_cases hDbelow : 2 * A.natDegree + B.natDegree <
          3 * U.natDegree
      · let R : k[X] := (-(320 : k)) • B ^ 4 +
            (-(320 * delta : k)) • (A ^ 2 * B) +
            gammaConstantCoreLowRest410 delta zeta eta theta A B U
        have hR : R.natDegree < 3 * U.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        have heqP : gammaConstantCorePrincipal410 A B U + R =
            C (q - 192 * gamma * c) := by
          dsimp only [X0, R] at heq ⊢
          rw [← heq]
          module
        exact False.elim ((smul_add_lower_ne_C410 (1 : k)
          (q - 192 * gamma * c) (gammaConstantCorePrincipal410 A B U) R
          (3 * U.natDegree) (by norm_num)
          (by intro hz; rw [hz, natDegree_zero] at hPdeg; omega)
          (by omega) hPdeg hR) (by simpa using heqP))
      · have hPD : 3 * U.natDegree <
            2 * A.natDegree + B.natDegree := by omega
        have hBD : 4 * B.natDegree <
            2 * A.natDegree + B.natDegree := by omega
        let R : k[X] := gammaConstantCorePrincipal410 A B U -
            (320 : k) • B ^ 4 +
            gammaConstantCoreLowRest410 delta zeta eta theta A B U
        have hR : R.natDegree < 2 * A.natDegree + B.natDegree := by
          dsimp only [R]
          compute_degree
          omega
        have hM : (A ^ 2 * B).natDegree =
            2 * A.natDegree + B.natDegree := by
          rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
        have heqD : (-(320 * delta : k)) • (A ^ 2 * B) + R =
            C (q - 192 * gamma * c) := by
          dsimp only [X0, R] at heq ⊢
          rw [← heq]
          module
        exact False.elim ((smul_add_lower_ne_C410 (-(320 * delta : k))
          (q - 192 * gamma * c) (A ^ 2 * B) R
          (2 * A.natDegree + B.natDegree)
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
          (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hM hR) heqD)
    · have hPB : 3 * U.natDegree < 4 * B.natDegree := by omega
      have hDB : 2 * A.natDegree + B.natDegree <
          4 * B.natDegree := by omega
      let R : k[X] := gammaConstantCorePrincipal410 A B U +
          (-(320 * delta : k)) • (A ^ 2 * B) +
          gammaConstantCoreLowRest410 delta zeta eta theta A B U
      have hR : R.natDegree < 4 * B.natDegree := by
        dsimp only [R]
        compute_degree
        omega
      have heqB : (-(320 : k)) • B ^ 4 + R =
          C (q - 192 * gamma * c) := by
        dsimp only [X0, R] at heq ⊢
        rw [← heq]
        module
      exact False.elim ((smul_add_lower_ne_C410 (-(320 : k))
        (q - 192 * gamma * c) (B ^ 4) R (4 * B.natDegree)
        (by norm_num) (pow_ne_zero 4 hB) (by omega)
        (by rw [natDegree_pow]) hR) heqB)

theorem discriminantInvariantTwo410_constantCore_eq_AB3_add_rest
    (gamma delta zeta eta theta c : k) (A B U : k[X])
    (hcoreC : gammaTieCore410 A B U = C c) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (2560 : k) • (A * B ^ 3) +
        ((480 * c : k) • B +
          gammaI2LoadRest410 gamma delta zeta eta theta A B U) := by
  have hU2 : U ^ 2 = (8 : k) • (A * B ^ 2) + C c := by
    have := hcoreC
    simp only [gammaTieCore410] at this
    linear_combination this
  rw [discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest,
    hU2]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_mul, map_pow,
    map_neg, RatFunc.algebraMap_C]
  simp only [map_ofNat]
  ring

theorem constantDiscriminantI2_gamma_constantCore_highRay_impossible
    (gamma delta zeta eta theta q c : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hcoreC : gammaTieCore410 A B U = C c)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) : False := by
  rw [discriminantInvariantTwo410_constantCore_eq_AB3_add_rest
    gamma delta zeta eta theta c A B U hcoreC] at hTwo
  let R : k[X] := (480 * c : k) • B +
    gammaI2LoadRest410 gamma delta zeta eta theta A B U
  have hR : R.natDegree < A.natDegree + 3 * B.natDegree := by
    dsimp only [R]
    simp only [gammaI2LoadRest410]
    compute_degree
    omega
  have hM : (A * B ^ 3).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  exact (smul_add_lower_ne_C410 (2560 : k) q (A * B ^ 3) R
    (A.natDegree + 3 * B.natDegree) (by norm_num)
    (mul_ne_zero hA (pow_ne_zero 3 hB)) (by omega) hM hR) hTwo

theorem gamma_constantCore_fixedTie_impossible
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : gammaTieCore410 A B U ≠ 0)
    (hcoreDegree : (gammaTieCore410 A B U).natDegree = 0)
    (htop : gammaTieCoreTopScalar410 A B U = 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2) : False := by
  obtain ⟨c, hcoreC'⟩ := natDegree_eq_zero.mp hcoreDegree
  have hcoreC : gammaTieCore410 A B U = C c := hcoreC'.symm
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    simp only [C_0] at hcoreC
    exact hcore hcoreC
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  rcases constantDiscriminantI1_gamma_constantCore_tie_rays
      gamma delta zeta eta theta q1 c A B U hA hB hU hUpos htie
        hcoreC htop hOne with hhigh | hlow
  · exact constantDiscriminantI2_gamma_constantCore_highRay_impossible
      gamma delta zeta eta theta q2 c A B U hA hB hU hUpos htie
        hhigh hcoreC hTwo
  · exact constantDiscriminantI2_gamma_fixedTie_coreZero_lowRay_impossible
      gamma delta zeta eta theta q2 A B U hB hU hendpoint htie hlow hTwo

def GammaCorePositiveTieDegreePacket410
    (K : ℕ) (A B U : k[X]) : Prop :=
  (0 < (gammaTieCore410 A B U).natDegree ∧
      (gammaTieCore410 A B U).natDegree < 2 * U.natDegree ∧
      gammaTieCoreTopScalar410 A B U = 0 ∧
      (gammaTieCore410 A B U).natDegree ≤ K) ∨
    ((gammaTieCore410 A B U).natDegree = 2 * U.natDegree ∧
      gammaTieCoreTopScalar410 A B U ≠ 0 ∧
      (gammaTieCore410 A B U).natDegree ≤ K)

def GammaI2ZeroFacePositiveCoreSelector410
    (L K : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      gammaTieCore410 A B U ≠ 0 ∧
      (∃ n : ℕ, A.natDegree = 2 * n ∧
        U.natDegree = B.natDegree + n) ∧
      GammaCorePositiveTieDegreePacket410 K A B U) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceCoreComponentSelector410_constant_elimination
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X]) (L K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hold : GammaI2ZeroFaceCoreComponentSelector410 L K A B U) :
    GammaI2ZeroFacePositiveCoreSelector410 L K A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · by_cases hAzero : A = 0
    · exact Or.inl hAzero
    right
    left
    refine ⟨htie.1, htie.2.1, htie.2.2.1, ?_⟩
    rcases htie.2.2.2 with hconstant | hdescended | hfull
    · exact (gamma_constantCore_fixedTie_impossible
        gamma delta zeta eta theta q1 q2 A B U hAzero hB hU hendpoint
          htie.1 htie.2.1 hconstant.1 hconstant.2 hOne hTwo).elim
    · exact Or.inl hdescended
    · exact Or.inr hfull
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionPositiveCoreFan410
    (delta zeta theta : k) (A B U : k[X]) (K : ℕ) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFacePositiveCoreSelector410
      (gammaI2DeltaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFacePositiveCoreSelector410
      (gammaI2ZetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFacePositiveCoreSelector410
        (gammaI2ThetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFacePositiveCoreSelector410
        (gammaI2BaseEnvelope410 B U) K A B U)

theorem gammaI2FirstCompetitionCoreComponentFan410_constant_elimination
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X]) (K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hold : GammaI2FirstCompetitionCoreComponentFan410
      delta zeta theta A B U K) :
    GammaI2FirstCompetitionPositiveCoreFan410 delta zeta theta A B U K := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceCoreComponentSelector410_constant_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2DeltaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceCoreComponentSelector410_constant_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2ZetaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceCoreComponentSelector410_constant_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2ThetaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceCoreComponentSelector410_constant_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2BaseEnvelope410 B U) K hB hU hendpoint hOne hTwo
            hbase.2.2.2⟩))

def ConstantCoreDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  CoreComponentRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionPositiveCoreFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)
      (max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

theorem coreComponentRefinedGammaNewtonResidual410_constant_elimination
    (gamma delta zeta eta theta k1 k2 : k) (A B C0 : k[X])
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hold : CoreComponentRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    ConstantCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  let K : ℕ := max
    (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
    (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hfan := gammaI2FirstCompetitionCoreComponentFan410_constant_elimination
    gamma delta zeta eta theta (2048 * k1) (2048 * k2) A B U K
      hold.1.1.1.1.1.1.2 hold.1.1.1.1.1.1.1.2
      hold.1.1.1.1.1.2 hOneD hTwoD hold.2
  simpa only [U, K] using hfan

/-! ## Source-facing deletion -/

def GammaConstantCoreDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      ConstantCoreDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaConstantCoreDeletedNoncubic_residual
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
    l = 0 ∧ GammaConstantCoreDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaCoreComponentNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hOne0 : firstIntegralOnePolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1, hgamma.1] using hOne
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      coreComponentRefinedGammaNewtonResidual410_constant_elimination
        gamma delta zeta eta theta k1 k2 A B C0 hOne0 hTwo0
          hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaConstantCoreDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaConstantCoreDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaConstantCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaConstantCoreDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaConstantCoreDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaConstantCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaConstantCoreTieElimination410

end Max11DegreeRoutes
