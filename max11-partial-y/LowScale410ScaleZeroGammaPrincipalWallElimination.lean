import LowScale410ScaleZeroGammaFullCoreScalarLeaves

/-!
# Elimination of the full-core principal gamma wall

On the remaining principal wall, the two tied fixed faces of the second
invariant have top coefficient `10240 * lc(A) * lc(B)^3`, hence cannot
cancel.  Constancy of the second invariant therefore forces their common
degree into the active later-load envelope.  This deletes the last genuine
full-core tie leaf while preserving the coordinate and envelope leaves.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaPrincipalWallElimination410

variable {k : Type*} [Field k] [CharZero k]

theorem gammaTie_principal_zero_implies_fixedI2_top
    (A B U : k[X]) (hU : U ≠ 0)
    (hprincipal : gammaTiePrincipalTopScalar410 A B U = 0) :
    gammaTieFixedI2TopScalar410 A B U =
      10240 * A.leadingCoeff * B.leadingCoeff ^ 3 := by
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hrel :
      24 * A.leadingCoeff * B.leadingCoeff ^ 2 - U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (40 : k) ≠ 0) hUlc))
    simp only [gammaTiePrincipalTopScalar410] at hprincipal
    linear_combination hprincipal
  simp only [gammaTieFixedI2TopScalar410]
  linear_combination -(480 * B.leadingCoeff) * hrel

theorem gammaTieFixedI2TopScalar410_ne_zero_of_principal
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hprincipal : gammaTiePrincipalTopScalar410 A B U = 0) :
    gammaTieFixedI2TopScalar410 A B U ≠ 0 := by
  rw [gammaTie_principal_zero_implies_fixedI2_top A B U hU hprincipal]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (leadingCoeff_ne_zero.mpr hA))
    (pow_ne_zero 3 (leadingCoeff_ne_zero.mpr hB))

theorem gammaTieFixedI2Face410_natDegree_eq_of_principal
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hprincipal : gammaTiePrincipalTopScalar410 A B U = 0) :
    (gammaTieFixedI2Face410 A B U).natDegree =
      A.natDegree + 3 * B.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simp only [gammaTieFixedI2Face410]
    compute_degree
    omega
  · rw [gammaTieFixedI2Face410_top_coeff A B U hA hB hU htie]
    exact gammaTieFixedI2TopScalar410_ne_zero_of_principal
      A B U hA hB hU hprincipal

theorem constantDiscriminantI2_gamma_principalTie_enters_envelope
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (L : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hprincipal : gammaTiePrincipalTopScalar410 A B U = 0)
    (hrest : (gammaI2LoadRest410
      gamma delta zeta eta theta A B U).natDegree ≤ L)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    A.natDegree + 3 * B.natDegree ≤ L := by
  by_contra hnot
  have hfaceDegree := gammaTieFixedI2Face410_natDegree_eq_of_principal
    A B U hA hB hU htie hprincipal
  have hface : gammaTieFixedI2Face410 A B U ≠ 0 := by
    intro hzero
    have htop := gammaTieFixedI2TopScalar410_ne_zero_of_principal
      A B U hA hB hU hprincipal
    apply htop
    rw [← gammaTieFixedI2Face410_top_coeff A B U hA hB hU htie, hzero,
      coeff_zero]
  have hrestlt : (gammaI2LoadRest410
      gamma delta zeta eta theta A B U).natDegree <
        A.natDegree + 3 * B.natDegree := by omega
  have hdecomp :=
    discriminantInvariantTwo410_eq_fixedFace_add_loadRest
      gamma delta zeta eta theta A B U
  rw [hdecomp] at hTwo
  exact (smul_add_lower_ne_C410 (1 : k) q
    (gammaTieFixedI2Face410 A B U)
    (gammaI2LoadRest410 gamma delta zeta eta theta A B U)
    (A.natDegree + 3 * B.natDegree) (by norm_num) hface
    (by omega) hfaceDegree hrestlt) (by simpa using hTwo)

def GammaI2ZeroFaceFullCoreTieDeletedSelector410
    (L : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceFullCorePrincipalSelector410_tie_deletion
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (L K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hrest : (gammaI2LoadRest410
      gamma delta zeta eta theta A B U).natDegree ≤ L)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2ZeroFaceFullCorePrincipalSelector410 L K A B U) :
    GammaI2ZeroFaceFullCoreTieDeletedSelector410 L A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · by_cases hAzero : A = 0
    · exact Or.inl hAzero
    · exact Or.inr (Or.inl
        (constantDiscriminantI2_gamma_principalTie_enters_envelope
          gamma delta zeta eta theta q A B U L hAzero hB hU htie.1
            htie.2.2.2.2 hrest hTwo))
  · exact Or.inr (Or.inl hABlow)
  · exact Or.inr (Or.inr hBUlow)

def GammaI2FirstCompetitionFullCoreTieDeletedFan410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceFullCoreTieDeletedSelector410
      (gammaI2DeltaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceFullCoreTieDeletedSelector410
      (gammaI2ZetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceFullCoreTieDeletedSelector410
        (gammaI2ThetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceFullCoreTieDeletedSelector410
        (gammaI2BaseEnvelope410 B U) A B U)

theorem gammaI2FirstCompetitionFullCorePrincipalFan410_tie_deletion
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q)
    (hold : GammaI2FirstCompetitionFullCorePrincipalFan410
      delta zeta theta A B U K) :
    GammaI2FirstCompetitionFullCoreTieDeletedFan410
      delta zeta theta A B U := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceFullCorePrincipalSelector410_tie_deletion
        gamma delta zeta eta theta q A B U
          (gammaI2DeltaEnvelope410 A B U) K hB hU
          (gammaI2LoadRest410_natDegree_le_deltaEnvelope
            gamma delta zeta eta theta A B U) hTwo hdelta.2⟩
  · rw [hzeta.1] at hTwo ⊢
    exact Or.inr (Or.inl ⟨rfl, hzeta.2.1,
      gammaI2ZeroFaceFullCorePrincipalSelector410_tie_deletion
        gamma 0 zeta eta theta q A B U
          (gammaI2ZetaEnvelope410 A B U) K hB hU
          (gammaI2LoadRest410_natDegree_le_zetaEnvelope
            gamma zeta eta theta A B U) hTwo hzeta.2.2⟩)
  · rw [htheta.1, htheta.2.1] at hTwo ⊢
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, htheta.2.2.1,
      gammaI2ZeroFaceFullCorePrincipalSelector410_tie_deletion
        gamma 0 0 eta theta q A B U
          (gammaI2ThetaEnvelope410 A B U) K hB hU
          (gammaI2LoadRest410_natDegree_le_thetaEnvelope
            gamma eta theta A B U) hTwo htheta.2.2.2⟩))
  · rw [hbase.1, hbase.2.1, hbase.2.2.1] at hTwo ⊢
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl,
      gammaI2ZeroFaceFullCorePrincipalSelector410_tie_deletion
        gamma 0 0 eta 0 q A B U
          (gammaI2BaseEnvelope410 B U) K hB hU
          (gammaI2LoadRest410_natDegree_le_baseEnvelope
            gamma eta A B U) hTwo hbase.2.2.2⟩))

def FullCorePrincipalWallDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionFullCoreTieDeletedFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)

theorem fullCoreHighScalarDeletedGammaNewtonResidual410_principal_elimination
    (gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hold : FullCoreHighScalarDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FullCorePrincipalWallDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold.1, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  let K : ℕ := max
    (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
    (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hdesc := hold.1
  have hfan := gammaI2FirstCompetitionFullCorePrincipalFan410_tie_deletion
    gamma delta zeta eta theta (2048 * k2) A B U K
      hdesc.1.1.1.1.1.1.1.1.2 hdesc.1.1.1.1.1.1.1.1.1.2
      hTwoD hold.2
  simpa only [U] using hfan

/-! ## Source-facing tie deletion -/

def GammaFullCorePrincipalWallDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCorePrincipalWallDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFullCorePrincipalWallDeletedNoncubic_residual
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
      GammaFullCorePrincipalWallDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaFullCoreHighScalarDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      fullCoreHighScalarDeletedGammaNewtonResidual410_principal_elimination
        gamma delta zeta eta theta k2 A B C0 hTwo0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFullCorePrincipalWallDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaFullCorePrincipalWallDeletedNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFullCorePrincipalWallDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFullCorePrincipalWallDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaFullCorePrincipalWallDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaFullCorePrincipalWallDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaPrincipalWallElimination410

end Max11DegreeRoutes
