import LowScale410ScaleZeroGammaHighUConeElimination

/-!
# Elimination of the first remaining broad gamma cone

We attack `3 deg B <= 2 deg A` away from the final cone
`deg B + 2 deg U <= 3 deg A`.  The already-closed high-`U` cone gives
`deg U < 3 deg B`.  Nonzero delta again exposes `delta A^4`; theta and the
base stratum expose `B^3 U`.  In the zeta stratum, the sole terminal tie
forces `3 deg A = 3 deg B + deg U`, where `B U^2` is uniquely dominant in
I2.  Thus only the final broad cone remains.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFirstConeElimination410

variable {k : Type*} [Field k] [CharZero k]

private theorem firstCone_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

theorem gamma_positive_highU_impossible
    (gamma delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U) : False := by
  have hrays := gamma_positive_highU_firstInvariant_rays
    gamma delta zeta eta theta q1 A B U hA hB hU hBpos hUpos hcone hOne
  rcases hrays with hdelta0 | hdeltane
  · rcases hfan with hdelta | hzeta | htheta | hbase
    · exact (hdelta.1 hdelta0.1).elim
    · have hTwoZ : discriminantInvariantTwoNumerator410
          0 0 gamma 0 zeta eta theta A B U = C q2 := by
        simpa only [hdelta0.1] using hTwo
      have hTerminalZ : lWallTerminalNumerator410
          0 0 gamma 0 zeta eta theta A B U = C terminal := by
        simpa only [hdelta0.1] using hTerminal
      exact gamma_highU_delta_zero_zeta_terminal_impossible
        gamma zeta eta theta q2 terminal A B U hzeta.2.1 hterminal
          hA hB hU hBpos hUpos hcone hdelta0.2 hTwoZ hTerminalZ
    · have hTwoT : discriminantInvariantTwoNumerator410
          0 0 gamma 0 0 eta theta A B U = C q2 := by
        simpa only [hdelta0.1, htheta.2.1] using hTwo
      have hTerminalT : lWallTerminalNumerator410
          0 0 gamma 0 0 eta theta A B U = C terminal := by
        simpa only [hdelta0.1, htheta.2.1] using hTerminal
      exact gamma_highU_delta_zeta_zero_theta_terminal_impossible
        gamma eta theta q2 terminal A B U htheta.2.2.1 hterminal
          hA hB hU hBpos hUpos hcone hdelta0.2 hTwoT hTerminalT
    · have hTwoB : discriminantInvariantTwoNumerator410
          0 0 gamma 0 0 eta 0 A B U = C q2 := by
        simpa only [hdelta0.1, hbase.2.1, hbase.2.2.1] using hTwo
      have hOneB : discriminantInvariantOneNumerator410
          0 0 gamma 0 0 eta 0 A B U = C q1 := by
        simpa only [hdelta0.1, hbase.2.1, hbase.2.2.1] using hOne
      exact gamma_highU_base_fixed_faces_impossible
        gamma eta q2 q1 A B U hA hB hU hBpos hUpos hcone hdelta0.2
          hTwoB hOneB
  · exact gamma_highU_delta_terminal_impossible
      gamma delta zeta eta theta q2 terminal A B U hdeltane.1 hterminal
        hA hB hU hBpos hUpos hcone hdeltane.2 hTwo hTerminal

theorem gamma_firstCone_delta_terminal_impossible
    (gamma delta zeta eta theta q2 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ 2 * A.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal) : False := by
  have hDerivative : derivative
      (gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B U) =
        C terminal := by
    rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
      gamma delta zeta eta theta q2 A B U hTwo]
    exact hTerminal
  have hDegree : (gammaLaterFiberPrimitive410
      gamma delta zeta theta q2 A B U).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B U)
      terminal hterminal hDerivative
  rw [gammaLaterFiberPrimitive410_eq_deltaA4_add_highBRest] at hDegree
  have hrest : (gammaHighBDeltaA4FiberRest410
      gamma delta zeta theta q2 A B U).natDegree < 4 * A.natDegree := by
    simp only [gammaHighBDeltaA4FiberRest410]
    compute_degree
    omega
  have hmain : ((560 * delta : k) • A ^ 4).natDegree =
      4 * A.natDegree := by
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
  rw [natDegree_add_eq_left_of_natDegree_lt (by
    rw [hmain]
    exact hrest), hmain] at hDegree
  omega

def gammaFirstConeZetaTerminalRest410
    (gamma zeta theta q2 : k) (A B U : k[X]) : k[X] :=
  -(2048 * gamma : k) • B ^ 3 - (3072 * zeta : k) • B ^ 2 -
    (1536 * zeta : k) • (A * U) + (3072 * theta : k) • A ^ 2 -
    (2048 * theta : k) • U - q2 • A

theorem gammaLaterFiberPrimitive410_delta_zero_eq_zetaA3_B3U_add_rest
    (gamma zeta theta q2 : k) (A B U : k[X]) :
    gammaLaterFiberPrimitive410 gamma 0 zeta theta q2 A B U =
      (1280 * zeta : k) • A ^ 3 + (1280 : k) • (B ^ 3 * U) +
        gammaFirstConeZetaTerminalRest410 gamma zeta theta q2 A B U := by
  simp [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaFirstConeZetaTerminalRest410]
  module

theorem gamma_firstCone_zeta_impossible
    (gamma zeta eta theta q2 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ 2 * A.natDegree)
    (hnotFinal : ¬ B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 zeta eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 zeta eta theta A B U = C terminal) : False := by
  have hApos : 0 < A.natDegree := by omega
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
  rw [gammaLaterFiberPrimitive410_delta_zero_eq_zetaA3_B3U_add_rest]
    at hDegree
  let P1 : k[X] := (1280 * zeta : k) • A ^ 3
  let P2 : k[X] := (1280 : k) • (B ^ 3 * U)
  let R : k[X] :=
    gammaFirstConeZetaTerminalRest410 gamma zeta theta q2 A B U
  have hP1 : P1 ≠ 0 := by
    dsimp only [P1]
    exact smul_ne_zero (mul_ne_zero (by norm_num) hzeta) (pow_ne_zero 3 hA)
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 3 hB) hU)
  have hP1deg : P1.natDegree = 3 * A.natDegree := by
    dsimp only [P1]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hzeta), natDegree_pow]
  have hP2deg : P2.natDegree = 3 * B.natDegree + U.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  have hR : R.natDegree < max P1.natDegree P2.natDegree := by
    dsimp only [R, gammaFirstConeZetaTerminalRest410]
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
  have htie := firstCone_twoTerm_degree_eq410 P1 P2 hP1 hP2 hbelow
  rw [hP1deg, hP2deg] at htie
  have hu2b : 2 * B.natDegree < U.natDegree := by omega
  rw [discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest]
    at hTwo
  let R2 : k[X] := (-(1280 : k)) • (A * B ^ 3) +
    gammaI2LoadRest410 gamma 0 zeta eta theta A B U
  have hform : (480 : k) • (B * U ^ 2) + R2 = C q2 := by
    dsimp only [R2]
    rw [← hTwo]
    abel
  have hR2 : R2.natDegree < B.natDegree + 2 * U.natDegree := by
    dsimp only [R2, gammaI2LoadRest410]
    compute_degree
    omega
  have hBU2deg : (B * U ^ 2).natDegree =
      B.natDegree + 2 * U.natDegree := by
    rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
  exact (smul_add_lower_ne_C410 (480 : k) q2 (B * U ^ 2) R2
    (B.natDegree + 2 * U.natDegree) (by norm_num)
    (mul_ne_zero hB (pow_ne_zero 2 hU)) (by omega) hBU2deg hR2) hform

theorem gamma_firstCone_theta_terminal_impossible
    (gamma eta theta q2 terminal : k) (A B U : k[X])
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ 2 * A.natDegree)
    (hnotFinal : ¬ B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 0 eta theta A B U = C terminal) : False := by
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
  let R : k[X] := (3072 * theta : k) • A ^ 2 +
    gammaHighBThetaFiberRest410 gamma theta q2 A B U
  have hform : (1280 : k) • (B ^ 3 * U) + R =
      gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U := by
    dsimp only [R]
    rw [gammaLaterFiberPrimitive410_theta_eq_two_faces_add_rest]
    abel
  have hR : R.natDegree < 3 * B.natDegree + U.natDegree := by
    dsimp only [R, gammaHighBThetaFiberRest410]
    compute_degree
    omega
  have hmain : ((1280 : k) • (B ^ 3 * U)).natDegree =
      3 * B.natDegree + U.natDegree := by
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  have hfull : (gammaLaterFiberPrimitive410
      gamma 0 0 theta q2 A B U).natDegree =
      3 * B.natDegree + U.natDegree := by
    rw [← hform, natDegree_add_eq_left_of_natDegree_lt]
    · exact hmain
    · rw [hmain]
      exact hR
  omega

theorem gamma_firstCone_base_terminal_impossible
    (gamma eta q2 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ 2 * A.natDegree)
    (hnotFinal : ¬ B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
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

def GammaFinalBroadConeSelector410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree

def FinalBroadConeGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaFinalBroadConeSelector410 A B (A ^ 2 - (4 : k) • C0)

def FinalBroadConeNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    FinalBroadConeGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_finalBroadConeNoncubic_residual
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
    l = 0 ∧ FinalBroadConeNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_highUConeDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hexact := constantIntegral410_exactOffTieFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hTwo0 : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2 := by
    simpa [hold.1, hold.2.1] using hTwo
  have hOne0 : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1 := by
    simpa [hold.1, hold.2.1] using hOne
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
  have hOneD : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C (2048 * k1) := by
    dsimp only [U]
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne0,
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
  rcases hsel.2.2.2.2.2 with hfirst | hfinal
  · by_cases hfinal' : B.natDegree + 2 * U.natDegree ≤
        3 * A.natDegree
    · exact hfinal'
    · by_cases hhighU : 3 * B.natDegree ≤ U.natDegree
      · exact (gamma_positive_highU_impossible
          gamma delta zeta eta theta (2048 * k2) (2048 * k1)
            (8192 * terminal) A B U
            (mul_ne_zero (by norm_num) hterminal)
            hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
            hsel.2.2.2.2.1 hhighU hTwoD hOneD hTerminalD hfan).elim
      · have hnotHighU : U.natDegree < 3 * B.natDegree := by omega
        rcases hfan with hdelta | hzeta | htheta | hbase
        · exact (gamma_firstCone_delta_terminal_impossible
            gamma delta zeta eta theta (2048 * k2) (8192 * terminal)
              A B U hdelta.1 (mul_ne_zero (by norm_num) hterminal)
              hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
              hsel.2.2.2.2.1 hfirst hnotHighU hTwoD hTerminalD).elim
        · have hTwoZ : discriminantInvariantTwoNumerator410
              0 0 gamma 0 zeta eta theta A B U = C (2048 * k2) := by
            simpa only [hzeta.1] using hTwoD
          have hTerminalZ : lWallTerminalNumerator410
              0 0 gamma 0 zeta eta theta A B U = C (8192 * terminal) := by
            simpa only [hzeta.1] using hTerminalD
          exact (gamma_firstCone_zeta_impossible gamma zeta eta theta
            (2048 * k2) (8192 * terminal) A B U hzeta.2.1
              (mul_ne_zero (by norm_num) hterminal)
              hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
              hsel.2.2.2.2.1 hfirst hfinal' hnotHighU hTwoZ hTerminalZ).elim
        · have hTwoT : discriminantInvariantTwoNumerator410
              0 0 gamma 0 0 eta theta A B U = C (2048 * k2) := by
            simpa only [htheta.1, htheta.2.1] using hTwoD
          have hTerminalT : lWallTerminalNumerator410
              0 0 gamma 0 0 eta theta A B U = C (8192 * terminal) := by
            simpa only [htheta.1, htheta.2.1] using hTerminalD
          exact (gamma_firstCone_theta_terminal_impossible gamma eta theta
            (2048 * k2) (8192 * terminal) A B U htheta.2.2.1
              (mul_ne_zero (by norm_num) hterminal)
              hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
              hsel.2.2.2.2.1 hfirst hfinal' hnotHighU hTwoT hTerminalT).elim
        · have hTwoB : discriminantInvariantTwoNumerator410
              0 0 gamma 0 0 eta 0 A B U = C (2048 * k2) := by
            simpa only [hbase.1, hbase.2.1, hbase.2.2.1] using hTwoD
          have hTerminalB : lWallTerminalNumerator410
              0 0 gamma 0 0 eta 0 A B U = C (8192 * terminal) := by
            simpa only [hbase.1, hbase.2.1, hbase.2.2.1] using hTerminalD
          exact (gamma_firstCone_base_terminal_impossible gamma eta
            (2048 * k2) (8192 * terminal) A B U
              (mul_ne_zero (by norm_num) hterminal)
              hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
              hsel.2.2.2.2.1 hfirst hfinal' hnotHighU hTwoB hTerminalB).elim
  · exact hfinal

theorem integrated410_finalBroadConeNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ FinalBroadConeNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_finalBroadConeNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_finalBroadConeNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        FinalBroadConeNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_finalBroadConeNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaFirstConeElimination410

end Max11DegreeRoutes
