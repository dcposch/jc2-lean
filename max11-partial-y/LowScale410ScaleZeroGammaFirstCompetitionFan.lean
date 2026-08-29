import LowScale410ScaleZeroGammaBUConstantEndpoint

/-!
# Full first `I₂` competition fan on the nonzero-gamma branch

After deleting `B = 0`, `U = 0`, and the constant `(B,U)` endpoint, the
gamma face `B*U` cannot be compared in isolation: the fixed zero-load faces
`A*B^3` and `B*U^2` may lie above it.  This file keeps those two faces exact
and bounds the arbitrary later-load remainder in four successive load strata.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFirstCompetitionFan410

variable {k : Type*} [Field k] [CharZero k]

def gammaI2LoadRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (320 * delta : k) • A ^ 3 + (768 * zeta : k) • A ^ 2 -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A +
    (1280 * delta : k) • B ^ 2 - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B - (1536 * zeta : k) • U

theorem discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        gammaI2LoadRest410 gamma delta zeta eta theta A B U := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [discriminantInvariantTwoNumerator410, gammaI2LoadRest410,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

def gammaI2DeltaEnvelope410 (A B U : k[X]) : ℕ :=
  max (B.natDegree + U.natDegree)
    (max (3 * A.natDegree)
      (max (A.natDegree + U.natDegree) (2 * B.natDegree)))

def gammaI2ZetaEnvelope410 (A B U : k[X]) : ℕ :=
  max (B.natDegree + U.natDegree) (2 * A.natDegree)

def gammaI2ThetaEnvelope410 (A B U : k[X]) : ℕ :=
  max (B.natDegree + U.natDegree) A.natDegree

def gammaI2BaseEnvelope410 (B U : k[X]) : ℕ :=
  B.natDegree + U.natDegree

private theorem gammaI2_natDegree_smul_le {p : k[X]} {L : ℕ}
    (c : k) (hp : p.natDegree ≤ L) : (c • p).natDegree ≤ L :=
  (natDegree_smul_le c p).trans hp

private theorem gammaI2_natDegree_add_le {p q : k[X]} {L : ℕ}
    (hp : p.natDegree ≤ L) (hq : q.natDegree ≤ L) :
    (p + q).natDegree ≤ L :=
  (natDegree_add_le p q).trans (max_le hp hq)

private theorem gammaI2_natDegree_sub_le {p q : k[X]} {L : ℕ}
    (hp : p.natDegree ≤ L) (hq : q.natDegree ≤ L) :
    (p - q).natDegree ≤ L :=
  (natDegree_sub_le p q).trans (max_le hp hq)

theorem gammaI2LoadRest410_natDegree_le_deltaEnvelope
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    (gammaI2LoadRest410 gamma delta zeta eta theta A B U).natDegree ≤
      gammaI2DeltaEnvelope410 A B U := by
  simp only [gammaI2LoadRest410, gammaI2DeltaEnvelope410]
  compute_degree
  omega

theorem gammaI2LoadRest410_natDegree_le_zetaEnvelope
    (gamma zeta eta theta : k) (A B U : k[X]) :
    (gammaI2LoadRest410 gamma 0 zeta eta theta A B U).natDegree ≤
      gammaI2ZetaEnvelope410 A B U := by
  simp only [gammaI2LoadRest410, zero_mul, mul_zero, zero_smul, zero_add,
    zero_sub, add_zero, sub_zero,
    gammaI2ZetaEnvelope410]
  let L := max (B.natDegree + U.natDegree) (2 * A.natDegree)
  have hA2 : ((768 * zeta : k) • A ^ 2).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    rw [natDegree_pow]
    dsimp only [L]
    omega
  have hA : ((2048 * theta : k) • A).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    dsimp only [L]
    omega
  have hBU : ((1536 * gamma : k) • (B * U)).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    exact natDegree_mul_le.trans (by dsimp only [L]; omega)
  have hB : ((4096 * eta : k) • B).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    dsimp only [L]
    omega
  have hU : ((1536 * zeta : k) • U).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    dsimp only [L]
    omega
  exact gammaI2_natDegree_sub_le
    (gammaI2_natDegree_add_le
      (gammaI2_natDegree_sub_le
        (gammaI2_natDegree_add_le hA2 hA) hBU) hB) hU

theorem gammaI2LoadRest410_natDegree_le_thetaEnvelope
    (gamma eta theta : k) (A B U : k[X]) :
    (gammaI2LoadRest410 gamma 0 0 eta theta A B U).natDegree ≤
      gammaI2ThetaEnvelope410 A B U := by
  simp only [gammaI2LoadRest410, zero_mul, mul_zero, zero_smul, zero_add,
    zero_sub, add_zero, sub_zero,
    gammaI2ThetaEnvelope410]
  let L := max (B.natDegree + U.natDegree) A.natDegree
  have hA : ((2048 * theta : k) • A).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    dsimp only [L]
    omega
  have hBU : ((1536 * gamma : k) • (B * U)).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    exact natDegree_mul_le.trans (by dsimp only [L]; omega)
  have hB : ((4096 * eta : k) • B).natDegree ≤ L := by
    apply gammaI2_natDegree_smul_le
    dsimp only [L]
    omega
  exact gammaI2_natDegree_add_le (gammaI2_natDegree_sub_le hA hBU) hB

theorem gammaI2LoadRest410_natDegree_le_baseEnvelope
    (gamma eta : k) (A B U : k[X]) :
    (gammaI2LoadRest410 gamma 0 0 eta 0 A B U).natDegree ≤
      gammaI2BaseEnvelope410 B U := by
  simp only [gammaI2LoadRest410, zero_mul, mul_zero, zero_smul, zero_add,
    zero_sub, add_zero, sub_zero,
    gammaI2BaseEnvelope410]
  apply gammaI2_natDegree_add_le
  · rw [natDegree_neg]
    apply gammaI2_natDegree_smul_le
    exact natDegree_mul_le
  · apply gammaI2_natDegree_smul_le
    omega

/-- The two fixed zero-load faces either tie, or at least one enters the
specified load envelope.  The `A = 0` coordinate leaf is kept explicit. -/
def GammaI2ZeroFaceSelector410 (L : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    A.natDegree + 3 * B.natDegree = B.natDegree + 2 * U.natDegree ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem constantDiscriminantI2_gamma_zeroFace_selector
    (gamma delta zeta eta theta q : k) (A B U : k[X]) (L : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hrest : (gammaI2LoadRest410 gamma delta zeta eta theta A B U).natDegree ≤ L)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    GammaI2ZeroFaceSelector410 L A B U := by
  by_cases hA : A = 0
  · exact Or.inl hA
  right
  let dAB : ℕ := A.natDegree + 3 * B.natDegree
  let dBU : ℕ := B.natDegree + 2 * U.natDegree
  by_cases htie : dAB = dBU
  · exact Or.inl htie
  right
  by_cases hABlow : dAB ≤ L
  · exact Or.inl hABlow
  right
  by_cases hBUlow : dBU ≤ L
  · exact hBUlow
  · have hdecomp :=
      discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest
        gamma delta zeta eta theta A B U
    rw [hdecomp] at hTwo
    rcases lt_or_gt_of_ne htie with hABBU | hBUAB
    · let R : k[X] := (-(1280 : k)) • (A * B ^ 3) +
          gammaI2LoadRest410 gamma delta zeta eta theta A B U
      have hR : R.natDegree < dBU := by
        dsimp only [R]
        compute_degree
        dsimp only [dAB, dBU] at hABBU hABlow hBUlow ⊢
        omega
      have hM : (B * U ^ 2).natDegree = dBU := by
        dsimp only [dBU]
        rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
      have heq : (480 : k) • (B * U ^ 2) + R = C q := by
        simpa [R, add_assoc, add_left_comm, add_comm] using hTwo
      exact False.elim ((smul_add_lower_ne_C410
        (480 : k) q (B * U ^ 2) R dBU
        (by norm_num) (mul_ne_zero hB (pow_ne_zero 2 hU))
        (by dsimp only [dBU] at hBUlow ⊢; omega) hM hR) heq)
    · let R : k[X] := (480 : k) • (B * U ^ 2) +
          gammaI2LoadRest410 gamma delta zeta eta theta A B U
      have hR : R.natDegree < dAB := by
        dsimp only [R]
        compute_degree
        dsimp only [dAB, dBU] at hBUAB hABlow hBUlow ⊢
        omega
      have hM : (A * B ^ 3).natDegree = dAB := by
        dsimp only [dAB]
        rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
      have heq : (-(1280 : k)) • (A * B ^ 3) + R = C q := by
        simpa [R, add_assoc] using hTwo
      exact False.elim ((smul_add_lower_ne_C410
        (-(1280 : k)) q (A * B ^ 3) R dAB
        (by norm_num) (mul_ne_zero hA (pow_ne_zero 3 hB))
        (by dsimp only [dAB] at hABlow ⊢; omega) hM hR) heq)

/-- Successively setting the absent earlier loads to zero gives a finite,
strictly sharper Newton fan for the two fixed `I₂` faces. -/
def GammaI2FirstCompetitionFan410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  (delta ≠ 0 ∧
      GammaI2ZeroFaceSelector410 (gammaI2DeltaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧
      GammaI2ZeroFaceSelector410 (gammaI2ZetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceSelector410 (gammaI2ThetaEnvelope410 A B U) A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceSelector410 (gammaI2BaseEnvelope410 B U) A B U)

theorem constantDiscriminantI2_gamma_firstCompetition_fan
    (gamma delta zeta eta theta q : k) (A B U : k[X])
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q) :
    GammaI2FirstCompetitionFan410 delta zeta theta A B U := by
  by_cases hdelta : delta = 0
  · subst delta
    by_cases hzeta : zeta = 0
    · subst zeta
      by_cases htheta : theta = 0
      · subst theta
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl,
          constantDiscriminantI2_gamma_zeroFace_selector
            gamma 0 0 eta 0 q A B U (gammaI2BaseEnvelope410 B U)
            hB hU (gammaI2LoadRest410_natDegree_le_baseEnvelope
              gamma eta A B U) hTwo⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, htheta,
          constantDiscriminantI2_gamma_zeroFace_selector
            gamma 0 0 eta theta q A B U (gammaI2ThetaEnvelope410 A B U)
            hB hU (gammaI2LoadRest410_natDegree_le_thetaEnvelope
              gamma eta theta A B U) hTwo⟩))
    · exact Or.inr (Or.inl ⟨rfl, hzeta,
        constantDiscriminantI2_gamma_zeroFace_selector
          gamma 0 zeta eta theta q A B U (gammaI2ZetaEnvelope410 A B U)
          hB hU (gammaI2LoadRest410_natDegree_le_zetaEnvelope
            gamma zeta eta theta A B U) hTwo⟩)
  · exact Or.inl ⟨hdelta,
      constantDiscriminantI2_gamma_zeroFace_selector
        gamma delta zeta eta theta q A B U (gammaI2DeltaEnvelope410 A B U)
        hB hU (gammaI2LoadRest410_natDegree_le_deltaEnvelope
          gamma delta zeta eta theta A B U) hTwo⟩

def FirstCompetitionFanRefinedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  BUConstantEndpointDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)

theorem BUConstantEndpointDeletedGammaNewtonResidual410_firstCompetition_refinement
    (gamma delta zeta eta theta k2 : k) (A B C0 : k[X])
    (hTwo : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2)
    (hold : BUConstantEndpointDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FirstCompetitionFanRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact constantDiscriminantI2_gamma_firstCompetition_fan
    gamma delta zeta eta theta (2048 * k2) A B U
      hold.1.2 hold.1.1.2 hTwoD

/-! ## Source-facing refinement -/

def GammaFirstCompetitionFanNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FirstCompetitionFanRefinedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFirstCompetitionFanNoncubic_residual
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
      GammaFirstCompetitionFanNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaBUConstantEndpointDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hTwo0 : firstIntegralTwoPolynomial410
        0 0 gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1, hgamma.1] using hTwo
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      BUConstantEndpointDeletedGammaNewtonResidual410_firstCompetition_refinement
        gamma delta zeta eta theta k2 A B C0 hTwo0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFirstCompetitionFanNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      GammaFirstCompetitionFanNoncubicEarlyLoadResidual410
        beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFirstCompetitionFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFirstCompetitionFanNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          GammaFirstCompetitionFanNoncubicEarlyLoadResidual410
            beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaFirstCompetitionFanNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFirstCompetitionFan410

end Max11DegreeRoutes
