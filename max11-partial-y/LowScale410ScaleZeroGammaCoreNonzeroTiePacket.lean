import LowScale410ScaleZeroGammaFirstTieCoreZeroElimination

/-!
# Component packet for the core-nonzero fixed-face tie

The exact degree tie has the parameterization `deg A = 2 n` and
`deg U = deg B + n`.  The retained second-core packet then splits the
nonzero core `G = U^2 - 8 A B^2` into three exact components: constant,
positive descended degree, or full degree `2 deg U`.  The first two have
vanishing top scalar; the full-degree component has nonvanishing top scalar.
-/

noncomputable section

set_option maxHeartbeats 6000000

open Polynomial

namespace Max11DegreeRoutes

section GammaCoreNonzeroTiePacket410

variable {k : Type*} [Field k] [CharZero k]

def gammaTieCore410 (A B U : k[X]) : k[X] :=
  U ^ 2 - (8 : k) • (A * B ^ 2)

def gammaTieCoreTopScalar410 (A B U : k[X]) : k :=
  U.leadingCoeff ^ 2 - 8 * A.leadingCoeff * B.leadingCoeff ^ 2

theorem gammaTieCore410_top_coeff
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree) :
    (gammaTieCore410 A B U).coeff (2 * U.natDegree) =
      gammaTieCoreTopScalar410 A B U := by
  have hU2deg : (U ^ 2).natDegree = 2 * U.natDegree := by
    rw [natDegree_pow]
  have hAB2deg : (A * B ^ 2).natDegree = 2 * U.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  rw [gammaTieCore410, coeff_sub, coeff_smul,
    show (U ^ 2).coeff (2 * U.natDegree) = U.leadingCoeff ^ 2 by
      rw [← hU2deg, coeff_natDegree, leadingCoeff_pow],
    show (A * B ^ 2).coeff (2 * U.natDegree) =
        A.leadingCoeff * B.leadingCoeff ^ 2 by
      rw [← hAB2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]]
  simp only [smul_eq_mul, gammaTieCoreTopScalar410]
  ring

theorem gammaTieCore410_natDegree_le_twoU
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree) :
    (gammaTieCore410 A B U).natDegree ≤ 2 * U.natDegree := by
  have hU2deg : (U ^ 2).natDegree = 2 * U.natDegree := by
    rw [natDegree_pow]
  have hAB2deg : (A * B ^ 2).natDegree = 2 * U.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have h8 : (8 : k) ≠ 0 := by norm_num
  exact (natDegree_sub_le _ _).trans (by rw [hU2deg,
    natDegree_smul _ h8, hAB2deg, max_self])

theorem gammaTieCore410_topScalar_eq_zero_of_degree_lt
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hdegree : (gammaTieCore410 A B U).natDegree < 2 * U.natDegree) :
    gammaTieCoreTopScalar410 A B U = 0 := by
  have hcoeff := coeff_eq_zero_of_natDegree_lt hdegree
  rw [gammaTieCore410_top_coeff A B U hA hB hU htie] at hcoeff
  exact hcoeff

theorem gammaTieCore410_topScalar_ne_zero_of_full_degree
    (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hcore : gammaTieCore410 A B U ≠ 0)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hdegree : (gammaTieCore410 A B U).natDegree = 2 * U.natDegree) :
    gammaTieCoreTopScalar410 A B U ≠ 0 := by
  intro hscalar
  have hcoeff : (gammaTieCore410 A B U).coeff (2 * U.natDegree) = 0 := by
    rw [gammaTieCore410_top_coeff A B U hA hB hU htie]
    exact hscalar
  have hlc : (gammaTieCore410 A B U).leadingCoeff = 0 := by
    rw [← hdegree, coeff_natDegree] at hcoeff
    exact hcoeff
  exact (leadingCoeff_ne_zero.mpr hcore) hlc

def GammaCoreNonzeroTieDegreePacket410
    (K : ℕ) (A B U : k[X]) : Prop :=
  ((gammaTieCore410 A B U).natDegree = 0 ∧
      gammaTieCoreTopScalar410 A B U = 0) ∨
    (0 < (gammaTieCore410 A B U).natDegree ∧
      (gammaTieCore410 A B U).natDegree < 2 * U.natDegree ∧
      gammaTieCoreTopScalar410 A B U = 0 ∧
      (gammaTieCore410 A B U).natDegree ≤ K) ∨
    ((gammaTieCore410 A B U).natDegree = 2 * U.natDegree ∧
      gammaTieCoreTopScalar410 A B U ≠ 0 ∧
      (gammaTieCore410 A B U).natDegree ≤ K)

theorem gamma_coreNonzero_fixedTie_degree_packet
    (A B U : k[X]) (K : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hUpos : 0 < U.natDegree)
    (htie : A.natDegree + 3 * B.natDegree =
      B.natDegree + 2 * U.natDegree)
    (hcore : gammaTieCore410 A B U ≠ 0)
    (hsecond : gammaTieCore410 A B U = 0 ∨
      (gammaTieCore410 A B U).natDegree = 0 ∨
      (gammaTieCore410 A B U).natDegree ≤ K) :
    (∃ n : ℕ, A.natDegree = 2 * n ∧ U.natDegree = B.natDegree + n) ∧
      GammaCoreNonzeroTieDegreePacket410 K A B U := by
  have hparam : ∃ n : ℕ,
      A.natDegree = 2 * n ∧ U.natDegree = B.natDegree + n := by
    refine ⟨U.natDegree - B.natDegree, ?_, ?_⟩ <;> omega
  refine ⟨hparam, ?_⟩
  rcases hsecond with hzero | hdegree0 | hcompetition
  · exact (hcore hzero).elim
  · left
    refine ⟨hdegree0, ?_⟩
    apply gammaTieCore410_topScalar_eq_zero_of_degree_lt
      A B U hA hB hU htie
    omega
  · by_cases hdegree0 : (gammaTieCore410 A B U).natDegree = 0
    · left
      refine ⟨hdegree0, ?_⟩
      apply gammaTieCore410_topScalar_eq_zero_of_degree_lt
        A B U hA hB hU htie
      omega
    right
    have hpositive : 0 < (gammaTieCore410 A B U).natDegree := by omega
    by_cases hfull : (gammaTieCore410 A B U).natDegree = 2 * U.natDegree
    · right
      exact ⟨hfull,
        gammaTieCore410_topScalar_ne_zero_of_full_degree
          A B U hA hB hU hcore htie hfull,
        hcompetition⟩
    · left
      have hle := gammaTieCore410_natDegree_le_twoU A B U hA hB hU htie
      have hlt : (gammaTieCore410 A B U).natDegree <
          2 * U.natDegree := by omega
      exact ⟨hpositive, hlt,
        gammaTieCore410_topScalar_eq_zero_of_degree_lt
          A B U hA hB hU htie hlt,
        hcompetition⟩

def GammaI2ZeroFaceCoreComponentSelector410
    (L K : ℕ) (A B U : k[X]) : Prop :=
  A = 0 ∨
    (A.natDegree + 3 * B.natDegree =
        B.natDegree + 2 * U.natDegree ∧
      gammaTieCore410 A B U ≠ 0 ∧
      (∃ n : ℕ, A.natDegree = 2 * n ∧
        U.natDegree = B.natDegree + n) ∧
      GammaCoreNonzeroTieDegreePacket410 K A B U) ∨
    A.natDegree + 3 * B.natDegree ≤ L ∨
    B.natDegree + 2 * U.natDegree ≤ L

theorem gammaI2ZeroFaceCoreNonzeroSelector410_component_refinement
    (A B U : k[X]) (L K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hsecond : gammaTieCore410 A B U = 0 ∨
      (gammaTieCore410 A B U).natDegree = 0 ∨
      (gammaTieCore410 A B U).natDegree ≤ K)
    (hold : GammaI2ZeroFaceCoreNonzeroSelector410 L A B U) :
    GammaI2ZeroFaceCoreComponentSelector410 L K A B U := by
  rcases hold with hA | htie | hABlow | hBUlow
  · exact Or.inl hA
  · by_cases hAzero : A = 0
    · exact Or.inl hAzero
    right
    left
    have hUpos : 0 < U.natDegree := by
      by_contra hnot
      have hU0 : U.natDegree = 0 := by omega
      have hB0 : B.natDegree = 0 := by omega
      exact hendpoint ⟨hB0, hU0⟩
    have hpacket := gamma_coreNonzero_fixedTie_degree_packet
      A B U K hAzero hB hU hUpos htie.1 htie.2 hsecond
    exact ⟨htie.1, htie.2, hpacket.1, hpacket.2⟩
  · exact Or.inr (Or.inr (Or.inl hABlow))
  · exact Or.inr (Or.inr (Or.inr hBUlow))

def GammaI2FirstCompetitionCoreComponentFan410
    (delta zeta theta : k) (A B U : k[X]) (K : ℕ) : Prop :=
  (delta ≠ 0 ∧ GammaI2ZeroFaceCoreComponentSelector410
      (gammaI2DeltaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta ≠ 0 ∧ GammaI2ZeroFaceCoreComponentSelector410
      (gammaI2ZetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
      GammaI2ZeroFaceCoreComponentSelector410
        (gammaI2ThetaEnvelope410 A B U) K A B U) ∨
    (delta = 0 ∧ zeta = 0 ∧ theta = 0 ∧
      GammaI2ZeroFaceCoreComponentSelector410
        (gammaI2BaseEnvelope410 B U) K A B U)

theorem gammaI2FirstCompetitionCoreNonzeroFan410_component_refinement
    (delta zeta theta : k) (A B U : k[X]) (K : ℕ)
    (hB : B ≠ 0) (hU : U ≠ 0)
    (hendpoint : ¬ (B.natDegree = 0 ∧ U.natDegree = 0))
    (hsecond : gammaTieCore410 A B U = 0 ∨
      (gammaTieCore410 A B U).natDegree = 0 ∨
      (gammaTieCore410 A B U).natDegree ≤ K)
    (hold : GammaI2FirstCompetitionCoreNonzeroFan410
      delta zeta theta A B U) :
    GammaI2FirstCompetitionCoreComponentFan410 delta zeta theta A B U K := by
  rcases hold with hdelta | hzeta | htheta | hbase
  · exact Or.inl ⟨hdelta.1,
      gammaI2ZeroFaceCoreNonzeroSelector410_component_refinement
        A B U (gammaI2DeltaEnvelope410 A B U) K hB hU hendpoint
          hsecond hdelta.2⟩
  · exact Or.inr (Or.inl ⟨hzeta.1, hzeta.2.1,
      gammaI2ZeroFaceCoreNonzeroSelector410_component_refinement
        A B U (gammaI2ZetaEnvelope410 A B U) K hB hU hendpoint
          hsecond hzeta.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htheta.1, htheta.2.1,
      htheta.2.2.1,
      gammaI2ZeroFaceCoreNonzeroSelector410_component_refinement
        A B U (gammaI2ThetaEnvelope410 A B U) K hB hU hendpoint
          hsecond htheta.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hbase.1, hbase.2.1,
      hbase.2.2.1,
      gammaI2ZeroFaceCoreNonzeroSelector410_component_refinement
        A B U (gammaI2BaseEnvelope410 B U) K hB hU hendpoint
          hsecond hbase.2.2.2⟩))

theorem firstTieCoreZeroDeletedGammaNewtonResidual410_secondCore
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hold : FirstTieCoreZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    GammaSecondCoreResidual410 delta zeta eta theta A B C0 := by
  rcases hold with ⟨hrays, _⟩
  rcases hrays with ⟨hdeleted, _⟩
  rcases hdeleted with ⟨hcompetition, _⟩
  rcases hcompetition with ⟨hBU, _⟩
  rcases hBU with ⟨hBzero, _⟩
  rcases hBzero with ⟨hUzero, _⟩
  rcases hUzero with ⟨hUrays, _⟩
  rcases hUrays with ⟨hUfan, _⟩
  rcases hUfan with ⟨hZeroB, _⟩
  rcases hZeroB with ⟨hZeroA, _⟩
  rcases hZeroA with ⟨hterminal, _⟩
  rcases hterminal with ⟨hcoordinate, _⟩
  exact hcoordinate.2

def CoreComponentRefinedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  FirstTieCoreZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaI2FirstCompetitionCoreComponentFan410 delta zeta theta A B
      (A ^ 2 - (4 : k) • C0)
      (max
        (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
        (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree)

theorem firstTieCoreZeroDeletedGammaNewtonResidual410_component_refinement
    (gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hold : FirstTieCoreZeroDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0) :
    CoreComponentRefinedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 := by
  refine ⟨hold, ?_⟩
  let U : k[X] := A ^ 2 - (4 : k) • C0
  let K : ℕ := max
    (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
    (gammaLaterOneRest410 delta zeta eta theta A B C0).natDegree
  have hsecond := firstTieCoreZeroDeletedGammaNewtonResidual410_secondCore
    gamma delta zeta eta theta A B C0 hold
  have hsecondU : gammaTieCore410 A B U = 0 ∨
      (gammaTieCore410 A B U).natDegree = 0 ∨
      (gammaTieCore410 A B U).natDegree ≤ K := by
    simpa [GammaSecondCoreResidual410, gammaLoadOneCorePolynomial410,
      gammaTieCore410, U, K] using hsecond
  have hfan := gammaI2FirstCompetitionCoreNonzeroFan410_component_refinement
    delta zeta theta A B U K hold.1.1.1.1.1.2
      hold.1.1.1.1.1.1.2 hold.1.1.1.1.2 hsecondU hold.2
  simpa only [U, K] using hfan

/-! ## Source-facing component packet -/

def GammaCoreComponentNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
      CoreComponentRefinedGammaNewtonResidual410
        gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

theorem constantIntegral410_gammaCoreComponentNoncubic_residual
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
    l = 0 ∧ GammaCoreComponentNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold :=
    constantIntegral410_gammaFirstTieCoreZeroDeletedNoncubic_residual
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hgamma | hdelta
  · left
    exact ⟨hgamma.1, hgamma.2.1, hgamma.2.2.1,
      firstTieCoreZeroDeletedGammaNewtonResidual410_component_refinement
        gamma delta zeta eta theta A B C0 hgamma.2.2.2⟩
  · exact Or.inr hdelta

theorem integrated410_gammaCoreComponentNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ GammaCoreComponentNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_gammaCoreComponentNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_gammaCoreComponentNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        GammaCoreComponentNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_gammaCoreComponentNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaCoreNonzeroTiePacket410

end Max11DegreeRoutes
