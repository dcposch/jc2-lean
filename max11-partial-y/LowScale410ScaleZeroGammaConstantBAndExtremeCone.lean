import LowScale410ScaleZeroGammaAZeroAndCollapsedFan

/-!
# Constant-`B` boundary and the low fixed-face extreme cone

For nonzero constant `B`, the first invariant exposes the degrees
`2a`, `a+u`, and `3u`.  Their finite tie rays are incompatible with the
leading face of the exact terminal primitive in every load stratum.  We
also delete the positive cone `a+2b <= u`, where `U^3` is uniquely dominant
in the first invariant.
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaConstantBAndExtremeCone410

variable {k : Type*} [Field k] [CharZero k]

private def gammaThreeDegreeTie410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
    (d2 = m ∧ d3 = m)

private theorem gamma_threeTerm_degree_tie410
    (P1 P2 P3 : k[X]) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hbelow : (P1 + P2 + P3).natDegree <
      max P1.natDegree (max P2.natDegree P3.natDegree)) :
    gammaThreeDegreeTie410 P1.natDegree P2.natDegree P3.natDegree
      (max P1.natDegree (max P2.natDegree P3.natDegree)) := by
  let m := max P1.natDegree (max P2.natDegree P3.natDegree)
  have h1le : P1.natDegree ≤ m := by dsimp [m]; omega
  have h2le : P2.natDegree ≤ m := by dsimp [m]; omega
  have h3le : P3.natDegree ≤ m := by dsimp [m]; omega
  have hcases : P1.natDegree = m ∨ P2.natDegree = m ∨ P3.natDegree = m := by
    dsimp [m]
    omega
  have hcoeff : (P1 + P2 + P3).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simpa only [m] using hbelow
  by_contra hnot
  change ¬ gammaThreeDegreeTie410 P1.natDegree P2.natDegree P3.natDegree m
    at hnot
  rcases hcases with h1 | h2 | h3
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [gammaThreeDegreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [gammaThreeDegreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [gammaThreeDegreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [gammaThreeDegreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [gammaThreeDegreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [gammaThreeDegreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree]]
      at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)

private theorem gamma_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

def gammaLaterTerminalPrimitive410
    (gamma delta zeta theta : k) (A B U : k[X]) : k[X] :=
  deltaLaterTerminalPrimitive410 delta zeta theta A B U -
    (2048 * gamma : k) • B ^ 3

def gammaLaterFiberPrimitive410
    (gamma delta zeta theta q2 : k) (A B U : k[X]) : k[X] :=
  gammaLaterTerminalPrimitive410 gamma delta zeta theta A B U - q2 • A

theorem lWallTerminal410_gammaLater_eq_derivative_sub
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    lWallTerminalNumerator410 0 0 gamma delta zeta eta theta A B U =
      derivative (gammaLaterTerminalPrimitive410
        gamma delta zeta theta A B U) -
        discriminantInvariantTwoNumerator410
          0 0 gamma delta zeta eta theta A B U * derivative A := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lWallTerminalNumerator410, lWallTerminalACoefficient410,
    lWallTerminalBCoefficient410, lWallTerminalUCoefficient410,
    discriminantInvariantTwoNumerator410,
    gammaLaterTerminalPrimitive410, deltaLaterTerminalPrimitive410,
    deltaTerminalPrimitive410, deltaLaterTerminalLoadPrimitive410,
    Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_smul, Polynomial.derivative_C,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C]
  simp only [zero_mul, mul_zero, zero_smul, add_zero, sub_zero, neg_zero,
    map_ofNat, map_natCast, map_one, map_neg, map_mul, map_zero]
  ring

theorem lWallTerminal410_gammaLater_eq_fiberDerivative
    (gamma delta zeta eta theta q2 : k) (A B U : k[X])
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2) :
    lWallTerminalNumerator410 0 0 gamma delta zeta eta theta A B U =
      derivative (gammaLaterFiberPrimitive410
        gamma delta zeta theta q2 A B U) := by
  rw [lWallTerminal410_gammaLater_eq_derivative_sub, hTwo]
  simp only [gammaLaterFiberPrimitive410, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.C_mul']

def gammaBConstantMiddleFace410 (gamma : k) (A B U : k[X]) : k[X] :=
  (960 : k) • (A * B ^ 2 * U) - (1536 * gamma : k) • (A * B ^ 2)

def gammaBConstantI1Rest410
    (delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(320 : k)) • B ^ 4 - (1536 * zeta : k) • (A * B) -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B -
    (1024 * eta : k) • U + (192 : k) • (0 : k[X])

theorem discriminantInvariantOne410_Bconstant_threeFaces
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(320 * delta) : k) • (A ^ 2 * B) +
        gammaBConstantMiddleFace410 gamma A B U + (-(40 : k)) • U ^ 3 +
          (gammaBConstantI1Rest410 delta zeta eta theta A B U +
            (192 * gamma : k) • U ^ 2) := by
  simp [discriminantInvariantOneNumerator410, gammaBConstantMiddleFace410,
    gammaBConstantI1Rest410]
  module

theorem gammaBConstantMiddleFace410_natDegree
    (gamma : k) (A B U : k[X]) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hB0 : B.natDegree = 0) (hUpos : 0 < U.natDegree) :
    (gammaBConstantMiddleFace410 gamma A B U).natDegree =
      A.natDegree + U.natDegree := by
  let R : k[X] := (-(1536 * gamma) : k) • (A * B ^ 2)
  have hform : gammaBConstantMiddleFace410 gamma A B U =
      (960 : k) • (A * B ^ 2 * U) + R := by
    dsimp only [R]
    simp only [gammaBConstantMiddleFace410]
    module
  have hmain : ((960 : k) • (A * B ^ 2 * U)).natDegree =
      A.natDegree + U.natDegree := by
    rw [natDegree_smul _ (by norm_num),
      natDegree_mul (mul_ne_zero hA (pow_ne_zero 2 hB)) hU,
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow, hB0]
    omega
  have hrest : R.natDegree < A.natDegree + U.natDegree := by
    dsimp only [R]
    compute_degree
    omega
  rw [hform, natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rw [hmain]
    exact hrest

theorem gamma_nonzero_constant_B_impossible
    (gamma delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hB0 : B.natDegree = 0) (hUpos : 0 < U.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U) : False := by
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
  have hmidDegree := gammaBConstantMiddleFace410_natDegree
    gamma A B U hA hB hU hB0 hUpos
  rw [discriminantInvariantOne410_Bconstant_threeFaces] at hOne
  by_cases hdelta : delta = 0
  · subst delta
    simp only [mul_zero, neg_zero, zero_smul, zero_add] at hOne
    let R : k[X] := gammaBConstantI1Rest410 0 zeta eta theta A B U +
      (192 * gamma : k) • U ^ 2
    have hsum : gammaBConstantMiddleFace410 gamma A B U +
        (-(40 : k)) • U ^ 3 = C q1 - R := by
      dsimp only [R]
      linear_combination hOne
    have hR : R.natDegree < max (A.natDegree + U.natDegree)
        (3 * U.natDegree) := by
      dsimp only [R]
      simp only [gammaBConstantI1Rest410]
      compute_degree
      omega
    have hbelow : (gammaBConstantMiddleFace410 gamma A B U +
        (-(40 : k)) • U ^ 3).natDegree <
          max (A.natDegree + U.natDegree) (3 * U.natDegree) := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt (max_lt
        (by rw [natDegree_C]; omega) hR)
    have heq := gamma_twoTerm_degree_eq410
      (gammaBConstantMiddleFace410 gamma A B U) ((-(40 : k)) • U ^ 3)
      (by
        intro hz
        have hd := congrArg Polynomial.natDegree hz
        rw [hmidDegree, natDegree_zero] at hd
        omega)
      (smul_ne_zero (by norm_num) (pow_ne_zero 3 hU))
      (by simpa only [hmidDegree,
        natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0), natDegree_pow]
          using hbelow)
    have ha : A.natDegree = 2 * U.natDegree := by
      have heq' : A.natDegree + U.natDegree = 3 * U.natDegree := by
        simpa only [hmidDegree,
        natDegree_smul _ (by norm_num : (-(40 : k)) ≠ 0), natDegree_pow]
          using heq
      omega
    rcases hfan with hbad | hzeta | htheta | hbase
    · exact (hbad.1 rfl).elim
    · let Rz : k[X] :=
        (1280 : k) • (B ^ 3 * U) -
          (3072 * zeta : k) • B ^ 2 -
          (1536 * zeta : k) • (A * U) +
          (3072 * theta : k) • A ^ 2 -
          (2048 * theta : k) • U -
          (2048 * gamma : k) • B ^ 3 - q2 • A
      have hform : gammaLaterFiberPrimitive410 gamma 0 zeta theta q2 A B U =
          (1280 * zeta : k) • A ^ 3 + Rz := by
        dsimp only [Rz]
        simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
          deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
          deltaLaterTerminalLoadPrimitive410, zero_mul, zero_smul, zero_add,
          add_zero, sub_zero]
        module
      have hrest : Rz.natDegree < 3 * A.natDegree := by
        dsimp only [Rz]
        compute_degree
        omega
      have hmain : ((1280 * zeta : k) • A ^ 3).natDegree =
          3 * A.natDegree := by
        rw [natDegree_smul _ (mul_ne_zero (by norm_num) hzeta.2.1),
          natDegree_pow]
      have hfull : (gammaLaterFiberPrimitive410
          gamma 0 zeta theta q2 A B U).natDegree = 3 * A.natDegree := by
        rw [hform, natDegree_add_eq_left_of_natDegree_lt]
        · exact hmain
        · rw [hmain]; exact hrest
      omega
    · have hzeta0 : zeta = 0 := htheta.2.1
      rw [hzeta0] at hDegree
      let Rt : k[X] :=
        (1280 : k) • (B ^ 3 * U) - (2048 * theta : k) • U -
          (2048 * gamma : k) • B ^ 3 - q2 • A
      have hform : gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B U =
          (3072 * theta : k) • A ^ 2 + Rt := by
        dsimp only [Rt]
        simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
          deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
          deltaLaterTerminalLoadPrimitive410, zero_mul, zero_smul, zero_add,
          add_zero, sub_zero]
        module
      have hrest : Rt.natDegree < 2 * A.natDegree := by
        dsimp only [Rt]
        compute_degree
        omega
      have hmain : ((3072 * theta : k) • A ^ 2).natDegree =
          2 * A.natDegree := by
        rw [natDegree_smul _ (mul_ne_zero (by norm_num) htheta.2.2.1),
          natDegree_pow]
      have hfull : (gammaLaterFiberPrimitive410
          gamma 0 0 theta q2 A B U).natDegree = 2 * A.natDegree := by
        rw [hform, natDegree_add_eq_left_of_natDegree_lt]
        · exact hmain
        · rw [hmain]; exact hrest
      omega
    · simp only [GammaBaseOffTieDegreeFan410] at hbase
      rcases hbase.2.2.2.2 with hAzero | hlow | hUzero
      · exact (hA hAzero).elim
      · omega
      · exact (by omega)
  · let R : k[X] := gammaBConstantI1Rest410 delta zeta eta theta A B U +
      (192 * gamma : k) • U ^ 2
    let P1 : k[X] := (-(320 * delta) : k) • (A ^ 2 * B)
    let P2 : k[X] := gammaBConstantMiddleFace410 gamma A B U
    let P3 : k[X] := (-(40 : k)) • U ^ 3
    let M : ℕ := max (2 * A.natDegree)
      (max (A.natDegree + U.natDegree) (3 * U.natDegree))
    have hsum : P1 + P2 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R]
      linear_combination hOne
    have hR : R.natDegree < M := by
      dsimp only [R, M]
      simp only [gammaBConstantI1Rest410]
      compute_degree
      omega
    have hbelow : (P1 + P2 + P3).natDegree < M := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C]; dsimp only [M]; omega) hR)
    have hP1 : P1 ≠ 0 := by
      dsimp only [P1]
      exact smul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
        (mul_ne_zero (pow_ne_zero 2 hA) hB)
    have hP2 : P2 ≠ 0 := by
      intro hz
      have hd := congrArg Polynomial.natDegree hz
      rw [hmidDegree, natDegree_zero] at hd
      omega
    have hP3 : P3 ≠ 0 := by
      dsimp only [P3]
      exact smul_ne_zero (by norm_num) (pow_ne_zero 3 hU)
    have hP1degree : P1.natDegree = 2 * A.natDegree := by
      dsimp only [P1]
      rw [natDegree_smul _
          (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)),
        natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow, hB0]
      omega
    have hP2degree : P2.natDegree = A.natDegree + U.natDegree := by
      exact hmidDegree
    have hP3degree : P3.natDegree = 3 * U.natDegree := by
      dsimp only [P3]
      rw [natDegree_smul _ (by norm_num), natDegree_pow]
    have htie := gamma_threeTerm_degree_tie410 P1 P2 P3 hP1 hP2 hP3
      (by
        rw [hP1degree, hP2degree, hP3degree]
        simpa only [M] using hbelow)
    rw [hP1degree, hP2degree, hP3degree] at htie
    simp only [gammaThreeDegreeTie410] at htie
    have hrays : A.natDegree = U.natDegree ∨
        2 * A.natDegree = 3 * U.natDegree ∨
        A.natDegree = 2 * U.natDegree := by
      omega
    let Rt : k[X] :=
      -(960 * delta : k) • (A ^ 2 * U) -
        (1280 * delta : k) • (A * B ^ 2) +
        (1280 : k) • (B ^ 3 * U) + (320 * delta : k) • U ^ 2 +
        (1280 * zeta : k) • A ^ 3 - (3072 * zeta : k) • B ^ 2 -
        (1536 * zeta : k) • (A * U) + (3072 * theta : k) • A ^ 2 -
        (2048 * theta : k) • U - (2048 * gamma : k) • B ^ 3 - q2 • A
    have hform : gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B U =
        (560 * delta : k) • A ^ 4 + Rt := by
      dsimp only [Rt]
      simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
        deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
        deltaLaterTerminalLoadPrimitive410]
      module
    have hrest : Rt.natDegree < 4 * A.natDegree := by
      dsimp only [Rt]
      compute_degree
      omega
    have hmain : ((560 * delta : k) • A ^ 4).natDegree =
        4 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta), natDegree_pow]
    have hfull : (gammaLaterFiberPrimitive410
        gamma delta zeta theta q2 A B U).natDegree = 4 * A.natDegree := by
      rw [hform, natDegree_add_eq_left_of_natDegree_lt]
      · exact hmain
      · rw [hmain]; exact hrest
    omega

def gammaLowFixedUConeI1Rest410
    (gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (-(320 * delta) : k) • (A ^ 2 * B) +
    (960 : k) • (A * B ^ 2 * U) -
    (1536 * gamma : k) • (A * B ^ 2) -
    (1536 * zeta : k) • (A * B) - (320 : k) • B ^ 4 -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

theorem discriminantInvariantOne410_eq_U3_add_lowFixedURest
    (gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B U =
      (-(40 : k)) • U ^ 3 +
        gammaLowFixedUConeI1Rest410 gamma delta zeta eta theta A B U := by
  simp [discriminantInvariantOneNumerator410, gammaLowFixedUConeI1Rest410]
  module

theorem gamma_positive_lowFixedU_cone_impossible
    (gamma delta zeta eta theta q1 : k) (A B U : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hBpos : 0 < B.natDegree) (hUpos : 0 < U.natDegree)
    (hcone : A.natDegree + 2 * B.natDegree ≤ U.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1) : False := by
  let R : k[X] := gammaLowFixedUConeI1Rest410
    gamma delta zeta eta theta A B U
  rw [discriminantInvariantOne410_eq_U3_add_lowFixedURest] at hOne
  have hform : (-(40 : k)) • U ^ 3 + R = C q1 := by
    simpa only [R] using hOne
  have hrest : R.natDegree < 3 * U.natDegree := by
    dsimp only [R, gammaLowFixedUConeI1Rest410]
    compute_degree
    omega
  exact (smul_add_lower_ne_C410 (-(40 : k)) q1 (U ^ 3) R
    (3 * U.natDegree) (by norm_num) (pow_ne_zero 3 hU) (by omega)
    (by rw [natDegree_pow]) hrest) hform

def GammaReducedPositiveOffTieCones410 (A B U : k[X]) : Prop :=
  3 * B.natDegree ≤ 2 * A.natDegree ∨
    3 * B.natDegree ≤ U.natDegree ∨
    B.natDegree + 2 * U.natDegree ≤ 3 * A.natDegree ∨
    2 * U.natDegree ≤ B.natDegree

def GammaConstantBDeletedSelector410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    (U.natDegree = 0 ∨
      (0 < B.natDegree ∧ 0 < U.natDegree ∧
        GammaReducedPositiveOffTieCones410 A B U))

def ConstantBDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaConstantBDeletedSelector410 A B (A ^ 2 - (4 : k) • C0)

def ConstantBDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    ConstantBDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_constantBDeletedNoncubic_residual
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
    l = 0 ∧ ConstantBDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hcollapsed := constantIntegral410_A_deletedCollapsedFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hexact := constantIntegral410_exactOffTieFanNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  have hTwo0 : firstIntegralTwoPolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k2 := by
    simpa [hcollapsed.1, hcollapsed.2.1] using hTwo
  have hOne0 : firstIntegralOnePolynomial410
      0 0 gamma delta zeta eta theta A B C0 = C k1 := by
    simpa [hcollapsed.1, hcollapsed.2.1] using hOne
  have hLower0 : lowerRowZeroPolynomial410
      (integratedWPolynomial410 0 alpha 0 gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 0 alpha 0 gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal := by
    simpa [hcollapsed.1, hcollapsed.2.1] using hLower
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
  have hdesc := hcollapsed.2.2.2.2.1
  have hA : A ≠ 0 := hcollapsed.2.2.2.2.2.1
  have hB : B ≠ 0 := hdesc.1.1.1.1.1.1.1.1.2
  have hU : U ≠ 0 := hdesc.1.1.1.1.1.1.1.1.1.2
  have hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U := by
    simpa only [U] using hexact.2.2.2.2.2
  refine ⟨hcollapsed.1, hcollapsed.2.1, hcollapsed.2.2.1,
    hcollapsed.2.2.2.1, hdesc, hA, hB, hU, ?_⟩
  rcases hcollapsed.2.2.2.2.2.2 with hboundary | hpositive
  · rcases hboundary with hB0 | hU0
    · exact (gamma_nonzero_constant_B_impossible
        gamma delta zeta eta theta (2048 * k2) (2048 * k1)
          (8192 * terminal) A B U (mul_ne_zero (by norm_num) hterminal)
          hA hB hU hB0
          (Nat.pos_of_ne_zero (fun hU0 =>
            hdesc.1.1.1.1.1.1.1.2 ⟨hB0, hU0⟩))
          hTwoD hOneD hTerminalD hfan).elim
    · exact Or.inl hU0
  · right
    refine ⟨hpositive.1, hpositive.2.1, ?_⟩
    rcases hpositive.2.2 with hlow | hrest
    · exact (gamma_positive_lowFixedU_cone_impossible
        gamma delta zeta eta theta (2048 * k1) A B U hA hB hU
          hpositive.1 hpositive.2.1 hlow hOneD).elim
    · simpa only [GammaReducedPositiveOffTieCones410] using hrest

theorem integrated410_constantBDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ ConstantBDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_constantBDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_constantBDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        ConstantBDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_constantBDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaConstantBAndExtremeCone410

end Max11DegreeRoutes
