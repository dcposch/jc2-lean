import LowScale410ScaleZeroGammaHighBThetaElimination

/-!
# Elimination of the positive high-`U` cone

On `3 deg B <= deg U`, the first invariant reduces to the three faces
`delta A^2 B`, `A B^2 U`, and `U^3`.  All nonzero-`delta` rays have the
unique terminal face `delta A^4`.  On the remaining ray
`deg A + 2 deg B = 2 deg U`, zeta and theta expose unique terminal faces,
while the base I1/I2 leading scalars are incompatible.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaHighUConeElimination410

variable {k : Type*} [Field k] [CharZero k]

private def highUThreeTie410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
    (d2 = m ∧ d3 = m)

private theorem highU_threeTerm_degree_tie410
    (P1 P2 P3 : k[X]) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hbelow : (P1 + P2 + P3).natDegree <
      max P1.natDegree (max P2.natDegree P3.natDegree)) :
    highUThreeTie410 P1.natDegree P2.natDegree P3.natDegree
      (max P1.natDegree (max P2.natDegree P3.natDegree)) := by
  let m := max P1.natDegree (max P2.natDegree P3.natDegree)
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨
      P3.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : (P1 + P2 + P3).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ highUThreeTie410 P1.natDegree P2.natDegree P3.natDegree m
    at hnot
  rcases hcases with h1 | h2 | h3
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highUThreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highUThreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highUThreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highUThreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highUThreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [highUThreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree]]
      at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)

private theorem highU_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

def gammaHighUInvariantOneRest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (320 : k) • B ^ 4 -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_highU_threeFaces
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(320 * delta) : k) • (A ^ 2 * B) +
        (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
        gammaHighUInvariantOneRest410 gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410,
    gammaHighUInvariantOneRest410]
  module

def GammaHighUFirstInvariantRays410
    (delta : k) (A B U : k[X]) : Prop :=
  (delta = 0 ∧ A.natDegree + 2 * B.natDegree = 2 * U.natDegree) ∨
    (delta ≠ 0 ∧
      (A.natDegree = B.natDegree + U.natDegree ∨
        2 * A.natDegree + B.natDegree = 3 * U.natDegree ∨
        A.natDegree + 2 * B.natDegree = 2 * U.natDegree))

theorem gamma_positive_highU_firstInvariant_rays
    (gamma delta zeta eta theta q1 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ U.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1) :
    GammaHighUFirstInvariantRays410 delta A B U := by
  rw [discriminantInvariantOne410_highU_threeFaces] at hOne
  let P1 : k[X] := (-(320 * delta) : k) • (A ^ 2 * B)
  let P2 : k[X] := (960 : k) • (A * B ^ 2 * U)
  let P3 : k[X] := (-(40 : k)) • U ^ 3
  let R : k[X] := gammaHighUInvariantOneRest410
    gamma delta zeta eta theta A B U
  have hP2 : P2 ≠ 0 := by
    dsimp only [P2]
    exact smul_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero hA (pow_ne_zero 2 hB)) hU)
  have hP3 : P3 ≠ 0 := by
    dsimp only [P3]
    exact smul_ne_zero (by norm_num) (pow_ne_zero 3 hU)
  have hP2deg : P2.natDegree =
      A.natDegree + 2 * B.natDegree + U.natDegree := by
    dsimp only [P2]
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
  have hP3deg : P3.natDegree = 3 * U.natDegree := by
    dsimp only [P3]
    rw [natDegree_smul _ (by norm_num), natDegree_pow]
  by_cases hdelta : delta = 0
  · left
    refine ⟨hdelta, ?_⟩
    subst delta
    simp only [mul_zero, neg_zero, zero_smul, zero_add] at hOne
    have hsum : P2 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R]
      linear_combination hOne
    have hR : R.natDegree < max P2.natDegree P3.natDegree := by
      dsimp only [R, gammaHighUInvariantOneRest410]
      rw [hP2deg, hP3deg]
      compute_degree
      omega
    have hbelow : (P2 + P3).natDegree < max P2.natDegree P3.natDegree := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hP2deg, hP3deg]; omega) hR)
    have heq := highU_twoTerm_degree_eq410 P2 P3 hP2 hP3 hbelow
    rw [hP2deg, hP3deg] at heq
    omega
  · right
    refine ⟨hdelta, ?_⟩
    have hP1 : P1 ≠ 0 := by
      dsimp only [P1]
      exact smul_ne_zero
        (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
        (mul_ne_zero (pow_ne_zero 2 hA) hB)
    have hP1deg : P1.natDegree = 2 * A.natDegree + B.natDegree := by
      dsimp only [P1]
      rw [natDegree_smul _
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)),
        natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
    have hsum : P1 + P2 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R]
      linear_combination hOne
    have hR : R.natDegree <
        max P1.natDegree (max P2.natDegree P3.natDegree) := by
      dsimp only [R, gammaHighUInvariantOneRest410]
      rw [hP1deg, hP2deg, hP3deg]
      compute_degree
      omega
    have hbelow : (P1 + P2 + P3).natDegree <
        max P1.natDegree (max P2.natDegree P3.natDegree) := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hP1deg, hP2deg, hP3deg]; omega) hR)
    have htie := highU_threeTerm_degree_tie410
      P1 P2 P3 hP1 hP2 hP3 hbelow
    rw [hP1deg, hP2deg, hP3deg] at htie
    simp only [highUThreeTie410] at htie
    omega

theorem gamma_highU_delta_terminal_impossible
    (gamma delta zeta eta theta q2 terminal : k) (A B U : k[X])
    (hdelta : delta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ U.natDegree)
    (hrays : A.natDegree = B.natDegree + U.natDegree ∨
      2 * A.natDegree + B.natDegree = 3 * U.natDegree ∨
      A.natDegree + 2 * B.natDegree = 2 * U.natDegree)
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
    rcases hrays with hray | hray | hray <;> omega
  have hmain : ((560 * delta : k) • A ^ 4).natDegree =
      4 * A.natDegree := by
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
  rw [natDegree_add_eq_left_of_natDegree_lt (by
    rw [hmain]
    exact hrest), hmain] at hDegree
  rcases hrays with hray | hray | hray <;> omega

theorem gamma_highU_delta_zero_zeta_terminal_impossible
    (gamma zeta eta theta q2 terminal : k) (A B U : k[X])
    (hzeta : zeta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ U.natDegree)
    (hray : A.natDegree + 2 * B.natDegree = 2 * U.natDegree)
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

theorem gamma_highU_delta_zeta_zero_theta_terminal_impossible
    (gamma eta theta q2 terminal : k) (A B U : k[X])
    (htheta : theta ≠ 0) (hterminal : terminal ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ U.natDegree)
    (hray : A.natDegree + 2 * B.natDegree = 2 * U.natDegree)
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

def gammaHighUBaseI2Rest410 (gamma eta : k) (B U : k[X]) : k[X] :=
  -(1536 * gamma : k) • (B * U) + (4096 * eta : k) • B

def gammaHighUBaseI1Rest410
    (gamma eta : k) (A B U : k[X]) : k[X] :=
  -(1536 * gamma : k) • (A * B ^ 2) - (320 : k) • B ^ 4 +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantTwo410_base_fixed_faces
    (gamma eta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410
        0 0 gamma 0 0 eta 0 A B U =
      (-(1280 : k)) • (A * B ^ 3) + (480 : k) • (B * U ^ 2) +
        gammaHighUBaseI2Rest410 gamma eta B U := by
  simp [discriminantInvariantTwoNumerator410, gammaHighUBaseI2Rest410]
  module

theorem discriminantInvariantOne410_base_fixed_faces
    (gamma eta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma 0 0 eta 0 A B U =
      (960 : k) • (A * B ^ 2 * U) + (-(40 : k)) • U ^ 3 +
        gammaHighUBaseI1Rest410 gamma eta A B U := by
  simp [discriminantInvariantOneNumerator410, gammaHighUBaseI1Rest410]
  module

theorem gamma_highU_base_fixed_faces_impossible
    (gamma eta q2 q1 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : 3 * B.natDegree ≤ U.natDegree)
    (hray : A.natDegree + 2 * B.natDegree = 2 * U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma 0 0 eta 0 A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma 0 0 eta 0 A B U = C q1) : False := by
  rw [discriminantInvariantTwo410_base_fixed_faces] at hTwo
  rw [discriminantInvariantOne410_base_fixed_faces] at hOne
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
  have hLower2 : (gammaHighUBaseI2Rest410 gamma eta B U).natDegree < d2 := by
    dsimp only [d2, gammaHighUBaseI2Rest410]
    compute_degree
    omega
  have hLower1 : (gammaHighUBaseI1Rest410
      gamma eta A B U).natDegree < d1 := by
    dsimp only [d1, gammaHighUBaseI1Rest410]
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
  have hAlc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have hBlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  have hUlc : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hU
  have hFaceTwo : -(1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) +
      480 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hBlc)
    linear_combination hTwoCoeff
  have hFaceOne : 960 * (A.leadingCoeff * B.leadingCoeff ^ 2) -
      40 * U.leadingCoeff ^ 2 = 0 := by
    apply (mul_left_cancel₀ hUlc)
    linear_combination hOneCoeff
  have hzero : (10240 : k) * (A.leadingCoeff * B.leadingCoeff ^ 2) = 0 := by
    linear_combination hFaceTwo + 12 * hFaceOne
  exact (mul_ne_zero (by norm_num)
    (mul_ne_zero hAlc (pow_ne_zero 2 hBlc))) hzero

def GammaTwoBroadPositiveCones410 (A B U : k[X]) : Prop :=
  3 * B.natDegree ≤ 2 * A.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree

def GammaHighUConeDeletedSelector410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      GammaTwoBroadPositiveCones410 A B U

def HighUConeDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaHighUConeDeletedSelector410 A B (A ^ 2 - (4 : k) • C0)

def HighUConeDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    HighUConeDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_highUConeDeletedNoncubic_residual
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
    l = 0 ∧ HighUConeDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_highBConeDeletedNoncubic_residual
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
  simp only [GammaTwoBroadPositiveCones410]
  rcases hsel.2.2.2.2.2 with h1 | hhighU | h3
  · exact Or.inl h1
  · have hrays := gamma_positive_highU_firstInvariant_rays
      gamma delta zeta eta theta (2048 * k1) A B U
        hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
        hsel.2.2.2.2.1 hhighU hOneD
    rcases hrays with hdelta0 | hdeltane
    · have hray := hdelta0.2
      rcases hfan with hdelta | hzeta | htheta | hbase
      · exact (hdelta.1 hdelta0.1).elim
      · have hTwoZ : discriminantInvariantTwoNumerator410
            0 0 gamma 0 zeta eta theta A B U = C (2048 * k2) := by
          simpa only [hdelta0.1] using hTwoD
        have hTerminalZ : lWallTerminalNumerator410
            0 0 gamma 0 zeta eta theta A B U = C (8192 * terminal) := by
          simpa only [hdelta0.1] using hTerminalD
        exact (gamma_highU_delta_zero_zeta_terminal_impossible
          gamma zeta eta theta (2048 * k2) (8192 * terminal) A B U
            hzeta.2.1 (mul_ne_zero (by norm_num) hterminal)
            hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
            hsel.2.2.2.2.1 hhighU hray hTwoZ hTerminalZ).elim
      · have hTwoT : discriminantInvariantTwoNumerator410
            0 0 gamma 0 0 eta theta A B U = C (2048 * k2) := by
          simpa only [hdelta0.1, htheta.2.1] using hTwoD
        have hTerminalT : lWallTerminalNumerator410
            0 0 gamma 0 0 eta theta A B U = C (8192 * terminal) := by
          simpa only [hdelta0.1, htheta.2.1] using hTerminalD
        exact (gamma_highU_delta_zeta_zero_theta_terminal_impossible
          gamma eta theta (2048 * k2) (8192 * terminal) A B U
            htheta.2.2.1 (mul_ne_zero (by norm_num) hterminal)
            hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
            hsel.2.2.2.2.1 hhighU hray hTwoT hTerminalT).elim
      · have hTwoB : discriminantInvariantTwoNumerator410
            0 0 gamma 0 0 eta 0 A B U = C (2048 * k2) := by
          simpa only [hdelta0.1, hbase.2.1, hbase.2.2.1] using hTwoD
        have hOneB : discriminantInvariantOneNumerator410
            0 0 gamma 0 0 eta 0 A B U = C (2048 * k1) := by
          simpa only [hdelta0.1, hbase.2.1, hbase.2.2.1] using hOneD
        exact (gamma_highU_base_fixed_faces_impossible
          gamma eta (2048 * k2) (2048 * k1) A B U
            hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
            hsel.2.2.2.2.1 hhighU hray hTwoB hOneB).elim
    · exact (gamma_highU_delta_terminal_impossible
        gamma delta zeta eta theta (2048 * k2) (8192 * terminal) A B U
          hdeltane.1 (mul_ne_zero (by norm_num) hterminal)
          hsel.1 hsel.2.1 hsel.2.2.1 hsel.2.2.2.1
          hsel.2.2.2.2.1 hhighU hdeltane.2 hTwoD hTerminalD).elim
  · exact Or.inr h3

theorem integrated410_highUConeDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ HighUConeDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_highUConeDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_highUConeDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        HighUConeDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_highUConeDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaHighUConeElimination410

end Max11DegreeRoutes
