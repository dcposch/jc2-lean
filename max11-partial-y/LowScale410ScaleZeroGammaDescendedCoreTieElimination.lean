import LowScale410ScaleZeroGammaConstantCoreTieElimination

/-!
# Elimination for the descended positive gamma core

If `0 < deg G < 2 deg U`, the gamma-core contribution remains strictly
below the genuine degree-`3 deg U` first-invariant principal face.  The same
three-face Newton argument as in the constant-core case leaves two exact
rays, and the second invariant deletes both.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaDescendedCoreTieElimination410

variable {k : Type*} [Field k] [CharZero k]

/-- Abstract three-face Newton selector used by the descended-core branch. -/
theorem gammaTie_threeFace_exactRays410
    (delta q : k) (A B U P R : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hUpos : 0 < U.natDegree)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hPdeg : P.natDegree = 3 * U.natDegree)
    (hRdeg : R.natDegree < 3 * U.natDegree)
    (heq : P - (320 : k) • B ^ 4 +
      (-(320 * delta : k)) • (A ^ 2 * B) + R = C q) :
    4 * B.natDegree = 3 * U.natDegree ∨
      (delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree) := by
  by_cases hhigh : 4 * B.natDegree = 3 * U.natDegree
  · exact Or.inl hhigh
  by_cases hdelta : delta = 0
  · subst delta
    rcases lt_or_gt_of_ne hhigh with hBbelow | hPbelow
    · let S : k[X] := (-(320 : k)) • B ^ 4 + R
      have hS : S.natDegree < 3 * U.natDegree := by
        dsimp only [S]
        compute_degree
        omega
      have heqP : P + S = C q := by
        dsimp only [S] at heq ⊢
        simp only [mul_zero, neg_zero, zero_smul, add_zero] at heq ⊢
        rw [← heq]
        module
      exact False.elim ((smul_add_lower_ne_C410 (1 : k) q P S
        (3 * U.natDegree) (by norm_num)
        (by intro hz; rw [hz, natDegree_zero] at hPdeg; omega)
        (by omega) hPdeg hS) (by simpa using heqP))
    · let S : k[X] := P + R
      have hS : S.natDegree < 4 * B.natDegree := by
        dsimp only [S]
        compute_degree
        omega
      have heqB : (-(320 : k)) • B ^ 4 + S = C q := by
        dsimp only [S] at heq ⊢
        simp only [mul_zero, neg_zero, zero_smul, add_zero] at heq ⊢
        rw [← heq]
        module
      exact False.elim ((smul_add_lower_ne_C410 (-(320 : k)) q
        (B ^ 4) S (4 * B.natDegree) (by norm_num)
        (pow_ne_zero 4 hB) (by omega) (by rw [natDegree_pow]) hS) heqB)
  · by_cases hlow : 3 * B.natDegree = U.natDegree
    · exact Or.inr ⟨hdelta, hlow⟩
    have hDne : 3 * U.natDegree ≠
        2 * A.natDegree + B.natDegree := by omega
    by_cases hBbelow : 4 * B.natDegree < 3 * U.natDegree
    · by_cases hDbelow : 2 * A.natDegree + B.natDegree <
          3 * U.natDegree
      · let S : k[X] := (-(320 : k)) • B ^ 4 +
            (-(320 * delta : k)) • (A ^ 2 * B) + R
        have hS : S.natDegree < 3 * U.natDegree := by
          dsimp only [S]
          compute_degree
          omega
        have heqP : P + S = C q := by
          dsimp only [S] at heq ⊢
          rw [← heq]
          module
        exact False.elim ((smul_add_lower_ne_C410 (1 : k) q P S
          (3 * U.natDegree) (by norm_num)
          (by intro hz; rw [hz, natDegree_zero] at hPdeg; omega)
          (by omega) hPdeg hS) (by simpa using heqP))
      · have hPD : 3 * U.natDegree <
            2 * A.natDegree + B.natDegree := by omega
        have hBD : 4 * B.natDegree <
            2 * A.natDegree + B.natDegree := by omega
        let S : k[X] := P - (320 : k) • B ^ 4 + R
        have hS : S.natDegree < 2 * A.natDegree + B.natDegree := by
          dsimp only [S]
          compute_degree
          omega
        have hM : (A ^ 2 * B).natDegree =
            2 * A.natDegree + B.natDegree := by
          rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
        have heqD : (-(320 * delta : k)) • (A ^ 2 * B) + S = C q := by
          dsimp only [S] at heq ⊢
          rw [← heq]
          module
        exact False.elim ((smul_add_lower_ne_C410 (-(320 * delta : k)) q
          (A ^ 2 * B) S (2 * A.natDegree + B.natDegree)
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
          (mul_ne_zero (pow_ne_zero 2 hA) hB) (by omega) hM hS) heqD)
    · have hPB : 3 * U.natDegree < 4 * B.natDegree := by omega
      have hDB : 2 * A.natDegree + B.natDegree <
          4 * B.natDegree := by omega
      let S : k[X] := P + (-(320 * delta : k)) • (A ^ 2 * B) + R
      have hS : S.natDegree < 4 * B.natDegree := by
        dsimp only [S]
        compute_degree
        omega
      have heqB : (-(320 : k)) • B ^ 4 + S = C q := by
        dsimp only [S] at heq ⊢
        rw [← heq]
        module
      exact False.elim ((smul_add_lower_ne_C410 (-(320 : k)) q
        (B ^ 4) S (4 * B.natDegree) (by norm_num)
        (pow_ne_zero 4 hB) (by omega) (by rw [natDegree_pow]) hS) heqB)

def gammaDescendedCoreLowRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (192 * gamma : k) • gammaTieCore410 A B U +
    gammaConstantCoreLowRest410 delta zeta eta theta A B U

theorem discriminantInvariantOne410_eq_descendedCore_threeFaces
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      gammaConstantCorePrincipal410 A B U - (320 : k) • B ^ 4 +
        (-(320 * delta : k)) • (A ^ 2 * B) +
        gammaDescendedCoreLowRest410
          gamma delta zeta eta theta A B U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantOneNumerator410,
    gammaConstantCorePrincipal410, gammaConstantCoreLowRest410,
    gammaDescendedCoreLowRest410, gammaTieCore410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem gammaDescendedCoreLowRest410_natDegree_lt_threeU
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hUpos : 0 < U.natDegree)
    (hcoreDegree : (gammaTieCore410 A B U).natDegree <
      2 * U.natDegree) :
    (gammaDescendedCoreLowRest410
      gamma delta zeta eta theta A B U).natDegree < 3 * U.natDegree := by
  simp only [gammaDescendedCoreLowRest410]
  have hlow := gammaConstantCoreLowRest410_natDegree_lt_threeU
    delta zeta eta theta A B U hA hB hU htie hUpos
  compute_degree
  omega

theorem constantDiscriminantI1_gamma_descendedCore_tie_rays
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (htop : gammaTieCoreTopScalar410 A B U = 0)
    (hcoreDegree : (gammaTieCore410 A B U).natDegree <
      2 * U.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    4 * B.natDegree = 3 * U.natDegree ∨
      (delta ≠ 0 ∧ 3 * B.natDegree = U.natDegree) := by
  rw [discriminantInvariantOne410_eq_descendedCore_threeFaces] at hOne
  exact gammaTie_threeFace_exactRays410 delta q A B U
    (gammaConstantCorePrincipal410 A B U)
    (gammaDescendedCoreLowRest410 gamma delta zeta eta theta A B U)
    hA hB hUpos htie
    (gammaConstantCorePrincipal410_natDegree_eq A B U hA hB hU htie htop)
    (gammaDescendedCoreLowRest410_natDegree_lt_threeU
      gamma delta zeta eta theta A B U hA hB hU htie hUpos hcoreDegree)
    hOne

theorem discriminantInvariantTwo410_eq_AB3_add_descendedCoreRest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (2560 : k) • (A * B ^ 3) +
        ((480 : k) • (B * gammaTieCore410 A B U) +
          gammaI2LoadRest410 gamma delta zeta eta theta A B U) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantTwoNumerator410, gammaTieCore410,
    gammaI2LoadRest410, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem constantDiscriminantI2_gamma_descendedCore_highRay_impossible
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hcoreDegree : (gammaTieCore410 A B U).natDegree <
      2 * U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) : False := by
  rw [discriminantInvariantTwo410_eq_AB3_add_descendedCoreRest] at hTwo
  let R : k[X] := (480 : k) • (B * gammaTieCore410 A B U) +
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

theorem gamma_descendedCore_fixedTie_impossible
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcoreDegree : 0 < (gammaTieCore410 A B U).natDegree ∧
      (gammaTieCore410 A B U).natDegree < 2 * U.natDegree)
    (htop : gammaTieCoreTopScalar410 A B U = 0)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2) : False := by
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  rcases constantDiscriminantI1_gamma_descendedCore_tie_rays
      gamma delta zeta eta theta q1 A B U hA hB hU hUpos htie htop
        hcoreDegree.2 hOne with hhigh | hlow
  · exact constantDiscriminantI2_gamma_descendedCore_highRay_impossible
      gamma delta zeta eta theta q2 A B U hA hB hU hUpos htie hhigh
        hcoreDegree.2 hTwo
  · exact constantDiscriminantI2_gamma_fixedTie_coreZero_lowRay_impossible
      gamma delta zeta eta theta q2 A B U hB hU hendpoint htie hlow hTwo

def GammaCoreFullTieDegreePacket410
    (K : ℕ) (A B U : k[X]) : Prop :=
  (gammaTieCore410 A B U).natDegree = 2 * U.natDegree ∧
    gammaTieCoreTopScalar410 A B U ≠ 0 ∧
    (gammaTieCore410 A B U).natDegree ≤ K

def GammaI2ZeroFaceFullCoreSelector410
    (L K : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      gammaTieCore410 A B U ≠ 0 ∧
      (∃ n : ℕ, A.natDegree = 2 * n ∧
        U.natDegree = B.natDegree + n) ∧
      GammaCoreFullTieDegreePacket410 K A B U) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFacePositiveCoreSelector410_descended_elimination
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X]) (L K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hold : GammaI2ZeroFacePositiveCoreSelector410 L K A B U) :
    GammaI2ZeroFaceFullCoreSelector410 L K A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · by_cases hAzero : A = 0
    · exact Or.inl hAzero
    right
    left
    refine ⟨htie.1, htie.2.1, htie.2.2.1, ?_⟩
    rcases htie.2.2.2 with hdescended | hfull
    · exact (gamma_descendedCore_fixedTie_impossible
        gamma delta zeta eta theta q1 q2 A B U hAzero hB hU hendpoint
          htie.1 ⟨hdescended.1, hdescended.2.1⟩ hdescended.2.2.1
          hOne hTwo).elim
    · exact hfull
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionFullCoreFan410
    (delta zeta theta : k) (A B U : k[X]) (K : ℕ) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceFullCoreSelector410
      (gammaI2DeltaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceFullCoreSelector410
      (gammaI2ZetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceFullCoreSelector410
        (gammaI2ThetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceFullCoreSelector410
        (gammaI2BaseEnvelope410 B U) K A B U)

theorem gammaI2FirstCompetitionPositiveCoreFan410_descended_elimination
    (gamma delta zeta eta theta q1 q2 : k) (A B U : k[X]) (K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hold : GammaI2FirstCompetitionPositiveCoreFan410
      delta zeta theta A B U K) :
    GammaI2FirstCompetitionFullCoreFan410 delta zeta theta A B U K := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFacePositiveCoreSelector410_descended_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2DeltaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFacePositiveCoreSelector410_descended_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2ZetaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFacePositiveCoreSelector410_descended_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2ThetaEnvelope410 A B U) K hB hU hendpoint hOne hTwo
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFacePositiveCoreSelector410_descended_elimination
        gamma delta zeta eta theta q1 q2 A B U
          (gammaI2BaseEnvelope410 B U) K hB hU hendpoint hOne hTwo
            hbase.2.2.2⟩))

def DescendedCoreDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  ConstantCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionFullCoreFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)
      (max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

theorem constantCoreDeletedGammaNewtonResidual410_descended_elimination
    (gamma delta zeta eta theta k1 k2 : k) (A B C0 : k[X])
    (hOne : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1)
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hold : ConstantCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    DescendedCoreDeletedGammaNewtonResidual410
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
  have hfan := gammaI2FirstCompetitionPositiveCoreFan410_descended_elimination
    gamma delta zeta eta theta (2048 * k1) (2048 * k2) A B U K
      hold.1.1.1.1.1.1.1.2 hold.1.1.1.1.1.1.1.1.2
      hold.1.1.1.1.1.1.2 hOneD hTwoD hold.2
  simpa only [U, K] using hfan

/-! ## Source-facing deletion -/

def GammaDescendedCoreDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      DescendedCoreDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaDescendedCoreDeletedNoncubic_residual
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
    l = 0 ∧ GammaDescendedCoreDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaConstantCoreDeletedNoncubic_residual
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
      constantCoreDeletedGammaNewtonResidual410_descended_elimination
        gamma delta zeta eta theta k1 k2 A B C0 hOne0 hTwo0
          hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaDescendedCoreDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaDescendedCoreDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaDescendedCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaDescendedCoreDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaDescendedCoreDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaDescendedCoreDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaDescendedCoreTieElimination410

end Max11DegreeRoutes
