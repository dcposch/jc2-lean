import LowScale410ScaleZeroGammaFullCoreTieScalarPacket

/-!
# Deleting the high scalar leaf of the full gamma core tie

On the high ray the fixed second-invariant scalar cancellation also cancels
the first two top terminal contributions.  The remaining top terminal
coefficient is a nonzero multiple of
`lc(B)^3 * lc(U) * (3 deg B + deg U)`, a contradiction.  Thus the only
honest full-core scalar residual is the principal cancellation wall.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFullCoreScalarLeaves410

variable {k : Type*} [Field k] [CharZero k]

def gammaFullCoreHighTerminalFace410 (A B U : k[X]) : k[X] :=
  (1280 : k) • (A * B ^ 3 * derivative A) -
    (480 : k) • (B * U ^ 2 * derivative A) +
    (3840 : k) • (B ^ 2 * U * derivative B) +
    (1280 : k) • (B ^ 3 * derivative U)

def gammaFullCoreHighTerminalARest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (1920 * delta : k) • A ^ 3 + (3072 * zeta : k) • A ^ 2 -
    (1280 * delta : k) • (A * U) + (4096 * theta : k) • A -
    (2560 * delta : k) • B ^ 2 + (1536 * gamma : k) • (B * U) -
    (4096 * eta : k) • B

def gammaFullCoreHighTerminalBRest410
    (gamma delta zeta : k) (A B : k[X]) : k[X] :=
  -(2560 * delta : k) • (A * B) -
    (6144 * gamma : k) • B ^ 2 - (6144 * zeta : k) • B

def gammaFullCoreHighTerminalURest410
    (delta zeta theta : k) (A U : k[X]) : k[X] :=
  -(960 * delta : k) • A ^ 2 - (1536 * zeta : k) • A +
    (640 * delta : k) • U - C (2048 * theta)

def gammaFullCoreHighTerminalRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  gammaFullCoreHighTerminalARest410
      gamma delta zeta eta theta A B U * derivative A +
    gammaFullCoreHighTerminalBRest410 gamma delta zeta A B * derivative B +
    gammaFullCoreHighTerminalURest410 delta zeta theta A U * derivative U

theorem lWallTerminalACoefficient410_scaleZeroGamma_high_split
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalACoefficient410 0 0 gamma delta zeta eta theta A B U =
      (1280 : k) • (A * B ^ 3) - (480 : k) • (B * U ^ 2) +
        gammaFullCoreHighTerminalARest410
          gamma delta zeta eta theta A B U := by
  simp only [lWallTerminalACoefficient410,
    gammaFullCoreHighTerminalARest410]
  push_cast
  module

theorem lWallTerminalBCoefficient410_scaleZeroGamma_high_split
    (gamma delta zeta : k) (A B U : k[X]) :
    lWallTerminalBCoefficient410 0 0 gamma delta zeta A B U =
      (3840 : k) • (B ^ 2 * U) +
        gammaFullCoreHighTerminalBRest410 gamma delta zeta A B := by
  simp only [lWallTerminalBCoefficient410,
    gammaFullCoreHighTerminalBRest410]
  push_cast
  module

theorem lWallTerminalUCoefficient410_scaleZeroGamma_high_split
    (delta zeta theta : k) (A B U : k[X]) :
    lWallTerminalUCoefficient410 0 0 delta zeta theta A B U =
      (1280 : k) • B ^ 3 +
        gammaFullCoreHighTerminalURest410 delta zeta theta A U := by
  simp only [lWallTerminalUCoefficient410,
    gammaFullCoreHighTerminalURest410]
  push_cast
  module

theorem lWallTerminal410_scaleZeroGamma_eq_highFace_add_rest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 gamma delta zeta eta theta A B U =
      gammaFullCoreHighTerminalFace410 A B U +
        gammaFullCoreHighTerminalRest410
          gamma delta zeta eta theta A B U := by
  rw [lWallTerminalNumerator410,
    lWallTerminalACoefficient410_scaleZeroGamma_high_split,
    lWallTerminalBCoefficient410_scaleZeroGamma_high_split,
    lWallTerminalUCoefficient410_scaleZeroGamma_high_split]
  simp only [gammaFullCoreHighTerminalFace410,
    gammaFullCoreHighTerminalRest410, add_mul, sub_mul, smul_mul_assoc]
  module

theorem gammaFullCoreHighTerminalRest410_natDegree_lt
    (gamma delta zeta eta theta : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hUpos : 0 < U.natDegree) :
    (gammaFullCoreHighTerminalRest410
      gamma delta zeta eta theta A B U).natDegree <
        2 * A.natDegree + 3 * B.natDegree - 1 := by
  have hApos : 0 < A.natDegree := by omega
  have hBpos : 0 < B.natDegree := by omega
  simp only [gammaFullCoreHighTerminalRest410,
    gammaFullCoreHighTerminalARest410,
    gammaFullCoreHighTerminalBRest410,
    gammaFullCoreHighTerminalURest410]
  compute_degree
  omega

def gammaFullCoreHighTerminalTopScalar410 (A B U : k[X]) : k :=
  1280 * (A.leadingCoeff * B.leadingCoeff ^ 3) *
      (A.leadingCoeff * (A.natDegree : k)) -
    480 * (B.leadingCoeff * U.leadingCoeff ^ 2) *
      (A.leadingCoeff * (A.natDegree : k)) +
    3840 * (B.leadingCoeff ^ 2 * U.leadingCoeff) *
      (B.leadingCoeff * (B.natDegree : k)) +
    1280 * B.leadingCoeff ^ 3 *
      (U.leadingCoeff * (U.natDegree : k))

theorem gammaFullCoreHighTerminalFace410_top_coeff
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hUpos : 0 < U.natDegree) :
    (gammaFullCoreHighTerminalFace410 A B U).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) =
      gammaFullCoreHighTerminalTopScalar410 A B U := by
  have hApos : 0 < A.natDegree := by omega
  have hBpos : 0 < B.natDegree := by omega
  have hdA : derivative A ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hdB : derivative B ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hdU : derivative U ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hAB3A : (A * B ^ 3 * derivative A).natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 3 hB)) hdA,
      natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow,
      natDegree_derivative]
    omega
  have hBU2A : (B * U ^ 2 * derivative A).natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero hB (pow_ne_zero 2 hU)) hdA,
      natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow,
      natDegree_derivative]
    omega
  have hB2UB : (B ^ 2 * U * derivative B).natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hB) hU) hdB,
      natDegree_mul (pow_ne_zero 2 hB) hU, natDegree_pow,
      natDegree_derivative]
    omega
  have hB3U : (B ^ 3 * derivative U).natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by
    rw [natDegree_mul (pow_ne_zero 3 hB) hdU, natDegree_pow,
      natDegree_derivative]
    omega
  rw [gammaFullCoreHighTerminalFace410, coeff_add, coeff_add, coeff_sub,
    coeff_smul, coeff_smul, coeff_smul, coeff_smul,
    show (A * B ^ 3 * derivative A).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) =
          (A.leadingCoeff * B.leadingCoeff ^ 3) *
            (A.leadingCoeff * (A.natDegree : k)) by
      rw [← hAB3A, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_derivative],
    show (B * U ^ 2 * derivative A).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) =
          (B.leadingCoeff * U.leadingCoeff ^ 2) *
            (A.leadingCoeff * (A.natDegree : k)) by
      rw [← hBU2A, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_derivative],
    show (B ^ 2 * U * derivative B).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) =
          (B.leadingCoeff ^ 2 * U.leadingCoeff) *
            (B.leadingCoeff * (B.natDegree : k)) by
      rw [← hB2UB, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow, leadingCoeff_derivative],
    show (B ^ 3 * derivative U).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) =
          B.leadingCoeff ^ 3 *
            (U.leadingCoeff * (U.natDegree : k)) by
      rw [← hB3U, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_derivative]]
  simp only [smul_eq_mul, gammaFullCoreHighTerminalTopScalar410]
  ring

theorem gammaFullCoreHighTerminalTopScalar410_ne_zero
    (A B U : k[X]) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (hfixed : gammaTieFixedI2TopScalar410 A B U = 0) :
    gammaFullCoreHighTerminalTopScalar410 A B U ≠ 0 := by
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hsum : (3 * B.natDegree : k) + U.natDegree ≠ 0 := by
    exact_mod_cast (show 3 * B.natDegree + U.natDegree ≠ 0 by omega)
  have heq : gammaFullCoreHighTerminalTopScalar410 A B U =
      1280 * B.leadingCoeff ^ 3 * U.leadingCoeff *
        ((3 * B.natDegree : k) + U.natDegree) := by
    simp only [gammaFullCoreHighTerminalTopScalar410,
      gammaTieFixedI2TopScalar410] at hfixed ⊢
    push_cast
    linear_combination
      -(A.leadingCoeff * (A.natDegree : k)) * hfixed
  rw [heq]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hBlc)) hUlc)
      hsum

theorem gamma_fullCore_highScalar_terminal_impossible
    (gamma delta zeta eta theta terminal : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hray : 4 * B.natDegree = 3 * U.natDegree)
    (hfixed : gammaTieFixedI2TopScalar410 A B U = 0)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal) : False := by
  have hUpos : 0 < U.natDegree := by
    by_contra hnot
    have hU0 : U.natDegree = 0 := by omega
    have hB0 : B.natDegree = 0 := by omega
    exact hendpoint ⟨hB0, hU0⟩
  have hrest := gammaFullCoreHighTerminalRest410_natDegree_lt
    gamma delta zeta eta theta A B U hA hB hU htie hray hUpos
  have htop := gammaFullCoreHighTerminalFace410_top_coeff
    A B U hA hB hU htie hray hUpos
  have htopne := gammaFullCoreHighTerminalTopScalar410_ne_zero
    A B U hB hU hUpos hfixed
  rw [lWallTerminal410_scaleZeroGamma_eq_highFace_add_rest] at hTerminal
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff
      (2 * A.natDegree + 3 * B.natDegree - 1)) hTerminal
  rw [coeff_add, htop, coeff_eq_zero_of_natDegree_lt hrest,
    show (C terminal : k[X]).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      omega, add_zero] at hcoeff
  exact htopne hcoeff

def GammaFullCoreTiePrincipalWall410 (A B U : k[X]) : Prop :=
  gammaTiePrincipalTopScalar410 A B U = 0

def GammaI2ZeroFaceFullCorePrincipalSelector410
    (L K : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      gammaTieCore410 A B U ≠ 0 ∧
      (∃ n : ℕ, A.natDegree = 2 * n ∧
        U.natDegree = B.natDegree + n) ∧
      GammaCoreFullTieDegreePacket410 K A B U ∧
      GammaFullCoreTiePrincipalWall410 A B U) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceFullCoreScalarSelector410_high_deletion
    (gamma delta zeta eta theta terminal : k) (A B U : k[X]) (L K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hold : GammaI2ZeroFaceFullCoreScalarSelector410 L K A B U) :
    GammaI2ZeroFaceFullCorePrincipalSelector410 L K A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · by_cases hAzero : A = 0
    · exact Or.inl hAzero
    right
    left
    refine ⟨htie.1, htie.2.1, htie.2.2.1, htie.2.2.2.1, ?_⟩
    rcases htie.2.2.2.2 with hprincipal | hhigh
    · exact hprincipal
    · exact (gamma_fullCore_highScalar_terminal_impossible
        gamma delta zeta eta theta terminal A B U hAzero hB hU hendpoint
          htie.1 hhigh.1 hhigh.2.1 hTerminal).elim
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionFullCorePrincipalFan410
    (delta zeta theta : k) (A B U : k[X]) (K : ℕ) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceFullCorePrincipalSelector410
      (gammaI2DeltaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceFullCorePrincipalSelector410
      (gammaI2ZetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceFullCorePrincipalSelector410
        (gammaI2ThetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceFullCorePrincipalSelector410
        (gammaI2BaseEnvelope410 B U) K A B U)

theorem gammaI2FirstCompetitionFullCoreScalarFan410_high_deletion
    (gamma delta zeta eta theta terminal : k) (A B U : k[X]) (K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hold : GammaI2FirstCompetitionFullCoreScalarFan410
      delta zeta theta A B U K) :
    GammaI2FirstCompetitionFullCorePrincipalFan410
      delta zeta theta A B U K := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceFullCoreScalarSelector410_high_deletion
        gamma delta zeta eta theta terminal A B U
          (gammaI2DeltaEnvelope410 A B U) K hB hU hendpoint hTerminal
            hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceFullCoreScalarSelector410_high_deletion
        gamma delta zeta eta theta terminal A B U
          (gammaI2ZetaEnvelope410 A B U) K hB hU hendpoint hTerminal
            hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceFullCoreScalarSelector410_high_deletion
        gamma delta zeta eta theta terminal A B U
          (gammaI2ThetaEnvelope410 A B U) K hB hU hendpoint hTerminal
            htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceFullCoreScalarSelector410_high_deletion
        gamma delta zeta eta theta terminal A B U
          (gammaI2BaseEnvelope410 B U) K hB hU hendpoint hTerminal
            hbase.2.2.2⟩))

def FullCoreHighScalarDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionFullCorePrincipalFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)
      (max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

theorem fullCoreScalarRefinedGammaNewtonResidual410_high_deletion
    (gamma delta zeta eta theta terminal : k) (A B C0 : k[X])
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B
        (A ^ 2 - (4 : k) • C0) = C terminal)
    (hold : FullCoreScalarRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    FullCoreHighScalarDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold.1, ?_⟩
  have hdesc := hold.1
  exact gammaI2FirstCompetitionFullCoreScalarFan410_high_deletion
    gamma delta zeta eta theta terminal A B
      (A ^ 2 - (4 : k) • C0)
      (max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)
      hdesc.1.1.1.1.1.1.1.1.2 hdesc.1.1.1.1.1.1.1.1.1.2
      hdesc.1.1.1.1.1.1.1.2 hTerminal hold.2

/-! ## Source-facing deletion -/

def GammaFullCoreHighScalarDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      FullCoreHighScalarDeletedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaFullCoreHighScalarDeletedNoncubic_residual
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
    l = 0 ∧ GammaFullCoreHighScalarDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_gammaFullCoreScalarNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410
          0 alpha 0 gamma delta epsilon zeta theta A B C0)
        (integratedZPolynomial410
          0 alpha 0 gamma delta epsilon zeta eta iota A B C0) B C0 =
          C terminal := by
      simpa [hold.1, hgamma.1] using hLower
    have hTerminalD : lWallTerminalNumerator410
        0 0 gamma delta zeta eta theta A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
      rw [← lowerRow410_discriminantTerminalNumerator, hLower0,
        Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      fullCoreScalarRefinedGammaNewtonResidual410_high_deletion
        gamma delta zeta eta theta (8192 * terminal) A B C0 hTerminalD
          hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaFullCoreHighScalarDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaFullCoreHighScalarDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaFullCoreHighScalarDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaFullCoreHighScalarDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaFullCoreHighScalarDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined :=
    integrated410_gammaFullCoreHighScalarDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hterminal
        (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFullCoreScalarLeaves410

end Max11DegreeRoutes
