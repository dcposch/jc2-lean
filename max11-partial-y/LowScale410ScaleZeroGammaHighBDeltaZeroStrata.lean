import LowScale410ScaleZeroGammaHighBCommonDeltaElimination

/-!
# The exact load strata on the last high-`B`, `delta = 0` ray

On `deg A + deg U = 2 deg B` and `2 deg U <= deg B`, a nonzero zeta makes
`zeta A^3` uniquely dominant in the terminal fiber, while the base stratum
has the unique face `B^3 U`.  The theta stratum can survive only at
`deg B = 3 deg U`, `deg A = 5 deg U`, together with one explicit top-scalar
cancellation.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GammaHighBDeltaZeroStrata410

variable {k : Type*} [Field k] [CharZero k]

private theorem highBDeltaZero_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

def gammaHighBZetaA3FiberRest410
    (gamma zeta theta q2 : k) (A B U : k[X]) : k[X] :=
  (1280 : k) • (B ^ 3 * U) - (2048 * gamma : k) • B ^ 3 -
    (3072 * zeta : k) • B ^ 2 - (1536 * zeta : k) • (A * U) +
    (3072 * theta : k) • A ^ 2 - (2048 * theta : k) • U - q2 • A

theorem gammaLaterFiberPrimitive410_delta_zero_eq_zetaA3_add_rest
    (gamma zeta theta q2 : k) (A B U : k[X]) :
    gammaLaterFiberPrimitive410 gamma 0 zeta theta q2 A B U =
      (1280 * zeta : k) • A ^ 3 +
        gammaHighBZetaA3FiberRest410 gamma zeta theta q2 A B U := by
  simp [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaHighBZetaA3FiberRest410]
  module

theorem gamma_highB_delta_zero_zeta_impossible
    (gamma zeta eta theta q2 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 2 * U.natDegree ≤ B.natDegree)
    (hray : A.natDegree + U.natDegree = 2 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 zeta eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 zeta eta theta A B U = C terminal) : False := by
  have hDerivative : derivative
      (gammaLaterFiberPrimitive410 gamma 0 zeta theta q2 A B U) =
        C terminal := by
    rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
      gamma 0 zeta eta theta q2 A B U hTwo]
    exact hTerminal
  have hDegree : (gammaLaterFiberPrimitive410
      gamma 0 zeta theta q2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaLaterFiberPrimitive410 gamma 0 zeta theta q2 A B U)
      terminal hterminal hDerivative
  rw [gammaLaterFiberPrimitive410_delta_zero_eq_zetaA3_add_rest] at hDegree
  have hrest : (gammaHighBZetaA3FiberRest410
      gamma zeta theta q2 A B U).natDegree < 3 * A.natDegree := by
    simp only [gammaHighBZetaA3FiberRest410]
    compute_degree
    omega
  have hmain : ((1280 * zeta : k) • A ^ 3).natDegree =
      3 * A.natDegree := by
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hzeta), natDegree_pow]
  rw [natDegree_add_eq_left_of_natDegree_lt (by
    rw [hmain]
    exact hrest), hmain] at hDegree
  omega

def gammaHighBBaseFiberRest410 (gamma q2 : k) (A B : k[X]) : k[X] :=
  -(2048 * gamma : k) • B ^ 3 - q2 • A

theorem gammaLaterFiberPrimitive410_base_eq_B3U_add_rest
    (gamma q2 : k) (A B U : k[X]) :
    gammaLaterFiberPrimitive410 gamma 0 0 0 q2 A B U =
      (1280 : k) • (B ^ 3 * U) +
        gammaHighBBaseFiberRest410 gamma q2 A B := by
  simp [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaHighBBaseFiberRest410]
  module

theorem gamma_highB_delta_zeta_theta_zero_impossible
    (gamma eta q2 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hray : A.natDegree + U.natDegree = 2 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 eta 0 A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 0 eta 0 A B U = C terminal) : False := by
  have hDerivative : derivative
      (gammaLaterFiberPrimitive410 gamma 0 0 0 q2 A B U) = C terminal := by
    rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
      gamma 0 0 eta 0 q2 A B U hTwo]
    exact hTerminal
  have hDegree : (gammaLaterFiberPrimitive410
      gamma 0 0 0 q2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaLaterFiberPrimitive410 gamma 0 0 0 q2 A B U)
      terminal hterminal hDerivative
  rw [gammaLaterFiberPrimitive410_base_eq_B3U_add_rest] at hDegree
  have hrest : (gammaHighBBaseFiberRest410 gamma q2 A B).natDegree <
      3 * B.natDegree + U.natDegree := by
    simp only [gammaHighBBaseFiberRest410]
    compute_degree
    omega
  have hmain : ((1280 : k) • (B ^ 3 * U)).natDegree =
      3 * B.natDegree + U.natDegree := by
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  rw [natDegree_add_eq_left_of_natDegree_lt (by
    rw [hmain]
    exact hrest), hmain] at hDegree
  omega

def gammaHighBThetaFiberRest410
    (gamma theta q2 : k) (A B U : k[X]) : k[X] :=
  -(2048 * gamma : k) • B ^ 3 - (2048 * theta : k) • U - q2 • A

theorem gammaLaterFiberPrimitive410_theta_eq_two_faces_add_rest
    (gamma theta q2 : k) (A B U : k[X]) :
    gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U =
      (1280 : k) • (B ^ 3 * U) + (3072 * theta : k) • A ^ 2 +
        gammaHighBThetaFiberRest410 gamma theta q2 A B U := by
  simp [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaHighBThetaFiberRest410]
  module

def GammaHighBThetaTerminalPacket410
    (theta : k) (A B U : k[X]) : Prop :=
  B.natDegree = 3 * U.natDegree ∧
    A.natDegree = 5 * U.natDegree ∧
    (1280 : k) * (B.leadingCoeff ^ 3 * U.leadingCoeff) +
      3072 * theta * A.leadingCoeff ^ 2 = 0

theorem gamma_highB_delta_zeta_zero_theta_packet
    (gamma eta theta q2 terminal : k) (A B U : k[X])
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 2 * U.natDegree ≤ B.natDegree)
    (hray : A.natDegree + U.natDegree = 2 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 0 eta theta A B U = C terminal) :
    GammaHighBThetaTerminalPacket410 theta A B U := by
  have hDerivative : derivative
      (gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U) = C terminal := by
    rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
      gamma 0 0 eta theta q2 A B U hTwo]
    exact hTerminal
  have hDegree : (gammaLaterFiberPrimitive410
      gamma 0 0 theta q2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U)
      terminal hterminal hDerivative
  rw [gammaLaterFiberPrimitive410_theta_eq_two_faces_add_rest] at hDegree
  let P1 : k[X] := (1280 : k) • (B ^ 3 * U)
  let P2 : k[X] := (3072 * theta : k) • A ^ 2
  let R : k[X] := gammaHighBThetaFiberRest410 gamma theta q2 A B U
  have hP1 : P1 ≠ 0 := by
    dsimp only [P1]
    exact smul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 3 hB) hU)
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (mul_ne_zero (by norm_num) htheta) (pow_ne_zero 2 hA)
  have hP1deg : P1.natDegree = 3 * B.natDegree + U.natDegree := by
    dsimp only [P1]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  have hP2deg : P2.natDegree = 2 * A.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) htheta), natDegree_pow]
  have hR : R.natDegree < max P1.natDegree P2.natDegree := by
    dsimp only [R, gammaHighBThetaFiberRest410]
    rw [hP1deg, hP2deg]
    compute_degree
    omega
  have hbelow : (P1 + P2).natDegree < max P1.natDegree P2.natDegree := by
    have hsumDegree : (P1 + P2 + R).natDegree = 1 := by
      simpa only [P1, P2, R] using hDegree
    have hsum : P1 + P2 = (P1 + P2 + R) - R := by module
    rw [hsum]
    exact (natDegree_sub_le _ _).trans_lt
      (max_lt (by rw [hsumDegree, hP1deg, hP2deg]; omega) hR)
  have heq := highBDeltaZero_twoTerm_degree_eq410 P1 P2 hP1 hP2 hbelow
  rw [hP1deg, hP2deg] at heq
  have hb : B.natDegree = 3 * U.natDegree := by omega
  have ha : A.natDegree = 5 * U.natDegree := by omega
  refine ⟨hb, ha, ?_⟩
  let d : ℕ := 3 * B.natDegree + U.natDegree
  have hd : d = 2 * A.natDegree := by dsimp only [d]; omega
  have hdpos : 1 < d := by dsimp only [d]; omega
  have hcoeff : (P1 + P2 + R).coeff d = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [P1, P2, R, hDegree] using hdpos
  have hRlt : R.natDegree < d := by
    exact hR.trans_le (by rw [hP1deg, hP2deg, hd]; omega)
  have hB3Udeg : (B ^ 3 * U).natDegree =
      3 * B.natDegree + U.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  have hA2deg : (A ^ 2).natDegree = 2 * A.natDegree := by
    rw [natDegree_pow]
  have hP1coeff : P1.coeff d =
      (1280 : k) * (B.leadingCoeff ^ 3 * U.leadingCoeff) := by
    dsimp only [P1]
    rw [coeff_smul, show d = (B ^ 3 * U).natDegree by
      rw [hB3Udeg], coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
    simp only [smul_eq_mul]
  have hP2coeff : P2.coeff d =
      (3072 * theta : k) * A.leadingCoeff ^ 2 := by
    dsimp only [P2]
    rw [coeff_smul, show d = (A ^ 2).natDegree by
      rw [hA2deg]
      exact hd, coeff_natDegree, leadingCoeff_pow]
    simp only [smul_eq_mul]
  rw [coeff_add, coeff_add, hP1coeff, hP2coeff,
    coeff_eq_zero_of_natDegree_lt hRlt, add_zero] at hcoeff
  exact hcoeff

def GammaHighBThetaOnlyRay410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  delta = 0 ∧ zeta = 0 ∧ theta ≠ 0 ∧
    A.natDegree + U.natDegree = 2 * B.natDegree ∧
    GammaHighBThetaTerminalPacket410 theta A B U

def GammaHighBThetaOnlyPositiveCones410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree ∨
    (2 * U.natDegree ≤ B.natDegree ∧
      GammaHighBThetaOnlyRay410 delta zeta theta A B U)

def GammaHighBThetaOnlySelector410
    (delta zeta theta : k) (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      GammaHighBThetaOnlyPositiveCones410 delta zeta theta A B U

def HighBThetaOnlyGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaHighBThetaOnlySelector410
      delta zeta theta A B (A ^ 2 - (4 : k) • C0)

def HighBThetaOnlyNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    HighBThetaOnlyGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_highBThetaOnlyNoncubic_residual
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
    l = 0 ∧ HighBThetaOnlyNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_highBDeltaZeroNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hexact := constantIntegral410_exactOffTieFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hTwo0 : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2 := by
    simpa [hold.1, hold.2.1] using hTwo
  have hLower0 : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal := by
    simpa [hold.1, hold.2.1] using hLower
  let U : k[X] := A ^ 2 - (4 : k) • C0
  have hTwoD : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k2) := by
    dsimp only [U]
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hTerminalD : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C (8192 * terminal) := by
    dsimp only [U]
    rw [← lowerRow410_discriminantTerminalNumerator, hLower0,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hdesc := hold.2.2.2.2.1
  have hsel := hold.2.2.2.2.2
  have hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U := by
    simpa only [U] using hexact.2.2.2.2.2
  refine ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2.1,
    hdesc, hsel.1, hsel.2.1, hsel.2.2.1,
    hsel.2.2.2.1, hsel.2.2.2.2.1, ?_⟩
  simp only [GammaHighBThetaOnlyPositiveCones410]
  rcases hsel.2.2.2.2.2 with h1 | h2 | h3 | hhigh
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · right
    right
    right
    refine ⟨hhigh.1, ?_⟩
    have hdelta0 := hhigh.2.1
    have hray := hhigh.2.2
    rcases hfan with hdelta | hzeta | htheta | hbase
    · exact (hdelta.1 hdelta0).elim
    · have hTwoZ : discriminantInvariantTwoNumerator410
          0 0 gamma 0 zeta eta theta A B U = C (2048 * k2) := by
        simpa only [hdelta0] using hTwoD
      have hTerminalZ : lWallTerminalNumerator410
          0 0 gamma 0 zeta eta theta A B U = C (8192 * terminal) := by
        simpa only [hdelta0] using hTerminalD
      exact (gamma_highB_delta_zero_zeta_impossible
        gamma zeta eta theta (2048 * k2) (8192 * terminal) A B U
          hzeta.2.1 (mul_ne_zero (by norm_num) hterminal)
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 hhigh.1 hray hTwoZ hTerminalZ).elim
    · have hTwoT : discriminantInvariantTwoNumerator410
          0 0 gamma 0 0 eta theta A B U = C (2048 * k2) := by
        simpa only [hdelta0, htheta.2.1] using hTwoD
      have hTerminalT : lWallTerminalNumerator410
          0 0 gamma 0 0 eta theta A B U = C (8192 * terminal) := by
        simpa only [hdelta0, htheta.2.1] using hTerminalD
      exact ⟨hdelta0, htheta.2.1, htheta.2.2.1, hray,
        gamma_highB_delta_zeta_zero_theta_packet
          gamma eta theta (2048 * k2) (8192 * terminal) A B U
            htheta.2.2.1 (mul_ne_zero (by norm_num) hterminal)
            hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
            hsel.2.2.2.2.1 hhigh.1 hray hTwoT hTerminalT⟩
    · have hTwoB : discriminantInvariantTwoNumerator410
          0 0 gamma 0 0 eta 0 A B U = C (2048 * k2) := by
        simpa only [hdelta0, hbase.2.1, hbase.2.2.1] using hTwoD
      have hTerminalB : lWallTerminalNumerator410
          0 0 gamma 0 0 eta 0 A B U = C (8192 * terminal) := by
        simpa only [hdelta0, hbase.2.1, hbase.2.2.1] using hTerminalD
      exact (gamma_highB_delta_zeta_theta_zero_impossible
        gamma eta (2048 * k2) (8192 * terminal) A B U
          (mul_ne_zero (by norm_num) hterminal)
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 hray hTwoB hTerminalB).elim

theorem integrated410_highBThetaOnlyNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ HighBThetaOnlyNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_highBThetaOnlyNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_highBThetaOnlyNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        HighBThetaOnlyNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_highBThetaOnlyNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaHighBDeltaZeroStrata410

end Max11DegreeRoutes
