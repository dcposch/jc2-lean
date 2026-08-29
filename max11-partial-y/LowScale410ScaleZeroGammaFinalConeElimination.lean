import LowScale410ScaleZeroGammaFirstConeElimination

/-!
# Elimination of the final positive gamma cone

After the high-`B` and high-`U` cones are removed, the last chamber has
`b < 2u`, `u < 3b`, and `b + 2u <= 3a`.  The delta terminal row forces
`4a = 3b + u`, after which `A B^3` is the unique I2 face.  In the zeta
stratum the terminal row and I2 force the two fixed ties, whose I1 and I2
top coefficients are incompatible.  The theta and base strata are excluded
by their exact off-tie selectors.  Thus the gamma branch is empty.
-/

noncomputable section

set_option maxHeartbeats 9000000

open Polynomial

namespace Max11DegreeRoutes

section GammaFinalConeElimination410

variable {k : Type*} [Field k] [CharZero k]

private theorem finalCone_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

theorem gamma_positive_highB_impossible
    (gamma delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 2 * U.natDegree ≤ B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U) : False := by
  have hrays := gamma_positive_highB_firstInvariant_rays
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
      exact gamma_highB_delta_zero_zeta_impossible
        gamma zeta eta theta q2 terminal A B U hzeta.2.1 hterminal
          hA hB hU hBpos hUpos hcone hdelta0.2 hTwoZ hTerminalZ
    · have hTwoT : discriminantInvariantTwoNumerator410
          0 0 gamma 0 0 eta theta A B U = C q2 := by
        simpa only [hdelta0.1, htheta.2.1] using hTwo
      have hTerminalT : lWallTerminalNumerator410
          0 0 gamma 0 0 eta theta A B U = C terminal := by
        simpa only [hdelta0.1, htheta.2.1] using hTerminal
      have hpacket := gamma_highB_delta_zeta_zero_theta_packet
        gamma eta theta q2 terminal A B U htheta.2.2.1 hterminal
          hA hB hU hBpos hUpos hcone hdelta0.2 hTwoT hTerminalT
      exact gamma_highB_theta_packet_impossible
        gamma eta theta q2 A B U hA hB hU hUpos hpacket hTwoT
    · have hTwoB : discriminantInvariantTwoNumerator410
          0 0 gamma 0 0 eta 0 A B U = C q2 := by
        simpa only [hdelta0.1, hbase.2.1, hbase.2.2.1] using hTwo
      have hTerminalB : lWallTerminalNumerator410
          0 0 gamma 0 0 eta 0 A B U = C terminal := by
        simpa only [hdelta0.1, hbase.2.1, hbase.2.2.1] using hTerminal
      exact gamma_highB_delta_zeta_theta_zero_impossible
        gamma eta q2 terminal A B U hterminal hA hB hU hBpos hUpos
          hdelta0.2 hTwoB hTerminalB
  · rcases hdeltane.2 with hray | hray | hray
    · exact gamma_highB_delta_two_A4_rays_impossible
        gamma delta zeta eta theta q2 terminal A B U hdeltane.1 hterminal
          hA hB hU hBpos hUpos hcone (Or.inl hray) hTwo hTerminal
    · exact gamma_highB_delta_two_A4_rays_impossible
        gamma delta zeta eta theta q2 terminal A B U hdeltane.1 hterminal
          hA hB hU hBpos hUpos hcone (Or.inr hray) hTwo hTerminal
    · exact gamma_highB_delta_common_A4_ray_impossible
        gamma delta zeta eta theta q2 terminal A B U hdeltane.1 hterminal
          hA hB hU hBpos hUpos hcone hray hTwo hTerminal

def gammaFinalConeDeltaFiberRest410
    (gamma delta zeta theta q2 : k) (A B U : k[X]) : k[X] :=
  (-(960 * delta) : k) • (A ^ 2 * U) -
    (1280 * delta : k) • (A * B ^ 2) + (320 * delta : k) • U ^ 2 +
    (1280 * zeta : k) • A ^ 3 - (3072 * zeta : k) • B ^ 2 -
    (1536 * zeta : k) • (A * U) + (3072 * theta : k) • A ^ 2 -
    (2048 * theta : k) • U - (2048 * gamma : k) • B ^ 3 - q2 • A

theorem gammaLaterFiberPrimitive410_eq_deltaA4_B3U_add_finalRest
    (gamma delta zeta theta q2 : k) (A B U : k[X]) :
    gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B U =
      (560 * delta : k) • A ^ 4 + (1280 : k) • (B ^ 3 * U) +
        gammaFinalConeDeltaFiberRest410 gamma delta zeta theta q2 A B U := by
  simp [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaFinalConeDeltaFiberRest410]
  module

theorem gamma_finalCone_delta_impossible
    (gamma delta zeta eta theta q2 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hfinal : B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighB : B.natDegree < 2 * U.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal) : False := by
  have hApos : 0 < A.natDegree := by omega
  have hu2a : U.natDegree < 2 * A.natDegree := by omega
  have h2b3a : 2 * B.natDegree < 3 * A.natDegree := by omega
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
  rw [gammaLaterFiberPrimitive410_eq_deltaA4_B3U_add_finalRest] at hDegree
  let P1 : k[X] := (560 * delta : k) • A ^ 4
  let P2 : k[X] := (1280 : k) • (B ^ 3 * U)
  let R : k[X] := gammaFinalConeDeltaFiberRest410
      gamma delta zeta theta q2 A B U
  have hP1 : P1 ≠ 0 := by
    dsimp only [P1]
    exact smul_ne_zero (mul_ne_zero (by norm_num) hdelta) (pow_ne_zero 4 hA)
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 3 hB) hU)
  have hP1deg : P1.natDegree = 4 * A.natDegree := by
    dsimp only [P1]
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
  have hP2deg : P2.natDegree = 3 * B.natDegree + U.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB) hU, natDegree_pow]
  have hR : R.natDegree < max P1.natDegree P2.natDegree := by
    dsimp only [R, gammaFinalConeDeltaFiberRest410]
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
  have htie := finalCone_twoTerm_degree_eq410 P1 P2 hP1 hP2 hbelow
  rw [hP1deg, hP2deg] at htie
  have hab : A.natDegree ≤ B.natDegree := by omega
  rw [discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest]
    at hTwo
  let R2 : k[X] := (480 : k) • (B * U ^ 2) +
    gammaI2LoadRest410 gamma delta zeta eta theta A B U
  have hR2 : R2.natDegree < A.natDegree + 3 * B.natDegree := by
    dsimp only [R2, gammaI2LoadRest410]
    compute_degree
    omega
  have hAB3deg : (A * B ^ 3).natDegree =
      A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hTwo' : (-(1280 : k)) • (A * B ^ 3) + R2 = C q2 := by
    dsimp only [R2]
    simpa [add_assoc] using hTwo
  exact (smul_add_lower_ne_C410 (-(1280 : k)) q2 (A * B ^ 3) R2
    (A.natDegree + 3 * B.natDegree) (by norm_num)
    (mul_ne_zero hA (pow_ne_zero 3 hB)) (by omega) hAB3deg hR2) hTwo'

theorem gamma_finalCone_zeta_terminal_tie
    (gamma zeta eta theta q2 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hfinal : B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighB : B.natDegree < 2 * U.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 zeta eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 zeta eta theta A B U = C terminal) :
    3 * A.natDegree = 3 * B.natDegree + U.natDegree := by
  have hApos : 0 < A.natDegree := by omega
  have hu2a : U.natDegree < 2 * A.natDegree := by omega
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
  have htie := finalCone_twoTerm_degree_eq410 P1 P2 hP1 hP2 hbelow
  simpa only [hP1deg, hP2deg] using htie

def gammaFinalConeZetaI1Rest410
    (gamma zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (320 : k) • B ^ 4 +
    (2048 * theta : k) • B + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantOne410_delta_zero_eq_fixedFaces_add_zetaRest
    (gamma zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma 0 zeta eta theta A B U =
      (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
        gammaFinalConeZetaI1Rest410 gamma zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410, gammaFinalConeZetaI1Rest410]
  module

theorem gamma_finalCone_zeta_impossible
    (gamma zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hfinal : B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighB : B.natDegree < 2 * U.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma 0 zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 zeta eta theta A B U = C terminal) : False := by
  have hApos : 0 < A.natDegree := by omega
  have hterminalTie := gamma_finalCone_zeta_terminal_tie
    gamma zeta eta theta q2 terminal A B U hzeta hterminal
      hA hB hU hBpos hUpos hfinal hnotHighB hnotHighU hTwo hTerminal
  rw [discriminantInvariantTwo410_scaleZero_eq_zeroFaces_add_loadRest]
    at hTwo
  let P1 : k[X] := (-(1280 : k)) • (A * B ^ 3)
  let P2 : k[X] := (480 : k) • (B * U ^ 2)
  let R2 : k[X] := gammaI2LoadRest410 gamma 0 zeta eta theta A B U
  have hP1 : P1 ≠ 0 := by
    dsimp only [P1]
    exact smul_ne_zero (by norm_num) (mul_ne_zero hA (pow_ne_zero 3 hB))
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (by norm_num) (mul_ne_zero hB (pow_ne_zero 2 hU))
  have hP1deg : P1.natDegree = A.natDegree + 3 * B.natDegree := by
    dsimp only [P1]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hP2deg : P2.natDegree = B.natDegree + 2 * U.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
  have hR2max : R2.natDegree < max P1.natDegree P2.natDegree := by
    exact (gammaI2LoadRest410_natDegree_le_zetaEnvelope
      gamma zeta eta theta A B U).trans_lt (by
        simp only [R2, gammaI2ZetaEnvelope410, hP1deg, hP2deg]
        omega)
  have hbelow : (P1 + P2).natDegree < max P1.natDegree P2.natDegree := by
    have hsum : P1 + P2 = C q2 - R2 := by
      dsimp only [P1, P2, R2]
      linear_combination hTwo
    rw [hsum]
    exact (natDegree_sub_le _ _).trans_lt
      (max_lt (by rw [natDegree_C, hP1deg, hP2deg]; omega) hR2max)
  have hfixed := finalCone_twoTerm_degree_eq410 P1 P2 hP1 hP2 hbelow
  rw [hP1deg, hP2deg] at hfixed
  have hfixed' : A.natDegree + 2 * B.natDegree = 2 * U.natDegree := by
    omega
  rw [discriminantInvariantOne410_delta_zero_eq_fixedFaces_add_zetaRest]
    at hOne
  let d2 : ℕ := A.natDegree + 3 * B.natDegree
  let d1 : ℕ := 3 * U.natDegree
  have hAB3deg : (A * B ^ 3).natDegree = d2 := by
    dsimp only [d2]
    rw [natDegree_mul hA (pow_ne_zero 3 hB), natDegree_pow]
  have hBU2deg : (B * U ^ 2).natDegree = d2 := by
    dsimp only [d2]
    rw [natDegree_mul hB (pow_ne_zero 2 hU), natDegree_pow]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = d1 := by
    dsimp only [d1]
    rw [natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    omega
  have hU3deg : (U ^ 3).natDegree = d1 := by
    dsimp only [d1]
    rw [natDegree_pow]
  have hLower2 : R2.natDegree < d2 := by
    exact hR2max.trans_le (by rw [hP1deg, hP2deg]; dsimp only [d2]; omega)
  have hLower1 : (gammaFinalConeZetaI1Rest410
      gamma zeta eta theta A B U).natDegree < d1 := by
    dsimp only [d1, gammaFinalConeZetaI1Rest410]
    compute_degree
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff d2) hTwo
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 3).coeff d2 =
        A.leadingCoeff * B.leadingCoeff ^ 3 by
      rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    show (B * U ^ 2).coeff d2 =
        B.leadingCoeff * U.leadingCoeff ^ 2 by
      rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hLower2, add_zero,
    show (C q2 : k[X]).coeff d2 = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      dsimp only [d2]
      omega] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff d1) hOne
  rw [coeff_add, coeff_add, coeff_smul, coeff_smul,
    show (A * B ^ 2 * U).coeff d1 =
        A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff by
      rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
        leadingCoeff_pow],
    show (U ^ 3).coeff d1 = U.leadingCoeff ^ 3 by
      rw [← hU3deg, coeff_natDegree, leadingCoeff_pow],
    coeff_eq_zero_of_natDegree_lt hLower1, add_zero,
    show (C q1 : k[X]).coeff d1 = 0 by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_C]
      dsimp only [d1]
      omega] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hFaceTwo : -(1280 : k) *
        (A.leadingCoeff * B.leadingCoeff ^ 2) +
      480 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hBlc)
    linear_combination hTwoCoeff
  have hFaceOne : 960 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
      40 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hUlc)
    linear_combination hOneCoeff
  have hzero : (10240 : k) *
      (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 12 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hA) (pow_ne_zero 2 hBlc))) hzero

theorem gamma_finalCone_theta_impossible
    (gamma eta theta q2 terminal : k) (A B U : k[X])
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hfinal : B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighB : B.natDegree < 2 * U.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hfan : GammaThetaOffTieDegreeFan410 A B U)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 eta theta A B U = C q2)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma 0 0 eta theta A B U = C terminal) : False := by
  rcases hfan with hA0 | hextreme | hB0 | hU0 | hthetaCone
  · exact (hA hA0).elim
  · omega
  · omega
  · omega
  · have hDerivative : derivative
        (gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U) =
          C terminal := by
      rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
        gamma 0 0 eta theta q2 A B U hTwo]
      exact hTerminal
    have hDegree : (gammaLaterFiberPrimitive410
        gamma 0 0 theta q2 A B U).natDegree = 1 :=
      natDegree_eq_one_of_derivative_eq_nonzero_C410
        (gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U)
        terminal hterminal hDerivative
    let R : k[X] := (1280 : k) • (B ^ 3 * U) +
      gammaHighBThetaFiberRest410 gamma theta q2 A B U
    have hform : (3072 * theta : k) • A ^ 2 + R =
        gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U := by
      dsimp only [R]
      rw [gammaLaterFiberPrimitive410_theta_eq_two_faces_add_rest]
      abel
    have hrest : R.natDegree < 2 * A.natDegree := by
      dsimp only [R, gammaHighBThetaFiberRest410]
      compute_degree
      omega
    have hmain : ((3072 * theta : k) • A ^ 2).natDegree =
        2 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) htheta), natDegree_pow]
    have hfull : (gammaLaterFiberPrimitive410
        gamma 0 0 theta q2 A B U).natDegree = 2 * A.natDegree := by
      rw [← hform, natDegree_add_eq_left_of_natDegree_lt]
      · exact hmain
      · rw [hmain]
        exact hrest
    omega

theorem gamma_finalCone_base_fan_impossible
    (A B U : k[X]) (hA : A ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hfinal : B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighB : B.natDegree < 2 * U.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hfan : GammaBaseOffTieDegreeFan410 A B U) : False := by
  rcases hfan with hA0 | hextreme | hU0
  · exact hA hA0
  · omega
  · omega

theorem gamma_finalCone_impossible
    (gamma delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hfinal : B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree)
    (hnotHighB : B.natDegree < 2 * U.natDegree)
    (hnotHighU : U.natDegree < 3 * B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U) : False := by
  rcases hfan with hdelta | hzeta | htheta | hbase
  · exact gamma_finalCone_delta_impossible
      gamma delta zeta eta theta q2 terminal A B U hdelta.1 hterminal
        hA hB hU hBpos hUpos hfinal hnotHighB hnotHighU hTwo hTerminal
  · have hTwoZ : discriminantInvariantTwoNumerator410
        0 0 gamma 0 zeta eta theta A B U = C q2 := by
      simpa only [hzeta.1] using hTwo
    have hOneZ : discriminantInvariantOneNumerator410
        0 0 gamma 0 zeta eta theta A B U = C q1 := by
      simpa only [hzeta.1] using hOne
    have hTerminalZ : lWallTerminalNumerator410
        0 0 gamma 0 zeta eta theta A B U = C terminal := by
      simpa only [hzeta.1] using hTerminal
    exact gamma_finalCone_zeta_impossible
      gamma zeta eta theta q2 q1 terminal A B U hzeta.2.1 hterminal
        hA hB hU hBpos hUpos hfinal hnotHighB hnotHighU
        hTwoZ hOneZ hTerminalZ
  · have hTwoT : discriminantInvariantTwoNumerator410
        0 0 gamma 0 0 eta theta A B U = C q2 := by
      simpa only [htheta.1, htheta.2.1] using hTwo
    have hTerminalT : lWallTerminalNumerator410
        0 0 gamma 0 0 eta theta A B U = C terminal := by
      simpa only [htheta.1, htheta.2.1] using hTerminal
    exact gamma_finalCone_theta_impossible
      gamma eta theta q2 terminal A B U htheta.2.2.1 hterminal
        hA hB hU hBpos hUpos hfinal hnotHighB hnotHighU
        htheta.2.2.2 hTwoT hTerminalT
  · exact gamma_finalCone_base_fan_impossible A B U hA hBpos hUpos
      hfinal hnotHighB hnotHighU hbase.2.2.2.2

theorem constantIntegral410_scaleZero_impossible
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
        iota A B C0) B C0 = C terminal) : False := by
  have hold := constantIntegral410_finalBroadConeNoncubic_residual
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
  have hsel := hold.2.2.2.2.2
  have hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U := by
    simpa only [U] using hexact.2.2.2.2.2
  by_cases hhighB : 2 * U.natDegree ≤ B.natDegree
  · exact gamma_positive_highB_impossible
      gamma delta zeta eta theta (2048 * k2) (2048 * k1)
        (8192 * terminal) A B U (mul_ne_zero (by norm_num) hterminal)
        hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
        hsel.2.2.2.2.1 hhighB hTwoD hOneD hTerminalD hfan
  · have hnotHighB : B.natDegree < 2 * U.natDegree := by omega
    by_cases hhighU : 3 * B.natDegree ≤ U.natDegree
    · exact gamma_positive_highU_impossible
        gamma delta zeta eta theta (2048 * k2) (2048 * k1)
          (8192 * terminal) A B U (mul_ne_zero (by norm_num) hterminal)
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 hhighU hTwoD hOneD hTerminalD hfan
    · have hnotHighU : U.natDegree < 3 * B.natDegree := by omega
      exact gamma_finalCone_impossible
        gamma delta zeta eta theta (2048 * k2) (2048 * k1)
          (8192 * terminal) A B U (mul_ne_zero (by norm_num) hterminal)
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 hsel.2.2.2.2.2 hnotHighB hnotHighU
          hTwoD hOneD hTerminalD hfan

theorem integrated410_scaleZero_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    False := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_scaleZero_impossible
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_impossible
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) : False := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  exact integrated410_scaleZero_impossible
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)

end GammaFinalConeElimination410

end Max11DegreeRoutes
