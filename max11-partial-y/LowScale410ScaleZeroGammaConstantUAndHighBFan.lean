import LowScale410ScaleZeroGammaConstantBAndExtremeCone

/-!
# Constant-`U` deletion and the high-`B` first-invariant rays

For nonzero constant `U`, the first invariant forces one of finitely many
`A`/`B` degree rays in each load stratum.  On every such ray the exact
terminal primitive has a unique top face, contradicting its forced degree
one.  On the remaining positive cone `2 deg U <= deg B`, the same first
invariant replaces the broad cone by three exact rays (two when `delta = 0`).
-/

noncomputable section

set_option maxHeartbeats 7000000

open Polynomial

namespace Max11DegreeRoutes

section GammaConstantUAndHighBFan410

variable {k : Type*} [Field k] [CharZero k]

private def constantUThreeTie410 (d1 d2 d3 m : ℕ) : Prop :=
  (d1 = m ∧ d2 = m) ∨ (d1 = m ∧ d3 = m) ∨
    (d2 = m ∧ d3 = m)

private theorem constantU_threeTerm_degree_tie410
    (P1 P2 P3 : k[X]) (hP1 : P1 ≠ 0) (hP2 : P2 ≠ 0) (hP3 : P3 ≠ 0)
    (hbelow : (P1 + P2 + P3).natDegree <
      max P1.natDegree (max P2.natDegree P3.natDegree)) :
    constantUThreeTie410 P1.natDegree P2.natDegree P3.natDegree
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
  change ¬ constantUThreeTie410 P1.natDegree P2.natDegree P3.natDegree m
    at hnot
  rcases hcases with h1 | h2 | h3
  · have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [constantUThreeTie410, h1, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [constantUThreeTie410, h1, heq])
    have h2lt : P2.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add,
      show P1.coeff m = P1.leadingCoeff by rw [← h1, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h2lt,
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP1) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [constantUThreeTie410, h2, heq])
    have h3ne : P3.natDegree ≠ m := by
      intro heq; exact hnot (by simp [constantUThreeTie410, h2, heq])
    have h1lt : P1.natDegree < m := by omega
    have h3lt : P3.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      show P2.coeff m = P2.leadingCoeff by rw [← h2, coeff_natDegree],
      coeff_eq_zero_of_natDegree_lt h3lt] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP2) (by simpa using hcoeff)
  · have h1ne : P1.natDegree ≠ m := by
      intro heq; exact hnot (by simp [constantUThreeTie410, h3, heq])
    have h2ne : P2.natDegree ≠ m := by
      intro heq; exact hnot (by simp [constantUThreeTie410, h3, heq])
    have h1lt : P1.natDegree < m := by omega
    have h2lt : P2.natDegree < m := by omega
    rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt h1lt,
      coeff_eq_zero_of_natDegree_lt h2lt,
      show P3.coeff m = P3.leadingCoeff by rw [← h3, coeff_natDegree]]
      at hcoeff
    exact (leadingCoeff_ne_zero.mpr hP3) (by simpa using hcoeff)

private theorem constantU_twoTerm_degree_eq410
    (P Q : k[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hbelow : (P + Q).natDegree < max P.natDegree Q.natDegree) :
    P.natDegree = Q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt] at hbelow
    omega
  · rw [natDegree_add_eq_left_of_natDegree_lt hgt] at hbelow
    omega

private theorem mul_C_eq_smul410 (P : k[X]) (u : k) :
    P * C u = u • P := by
  rw [Polynomial.smul_eq_C_mul]
  exact mul_comm _ _

def gammaConstantUI1GroundTail410
    (gamma delta eta theta u : k) (B : k[X]) : k[X] :=
  (-(640 * delta) : k) • (B * C u) + (2048 * theta : k) • B -
    (40 : k) • (C u) ^ 3 + (192 * gamma : k) • (C u) ^ 2 -
    (1024 * eta : k) • C u

theorem discriminantInvariantOne410_constant_U_decomposition
    (gamma delta zeta eta theta u : k) (A B : k[X]) :
    discriminantInvariantOneNumerator410
        0 0 gamma delta zeta eta theta A B (C u) =
      (-(320 * delta) : k) • (A ^ 2 * B) +
        (192 * (5 * u - 8 * gamma) : k) • (A * B ^ 2) +
        (-(320 : k)) • B ^ 4 +
      (-(1536 * zeta) : k) • (A * B) +
        gammaConstantUI1GroundTail410 gamma delta eta theta u B := by
  simp only [discriminantInvariantOneNumerator410,
    gammaConstantUI1GroundTail410, zero_mul, mul_zero, zero_smul, add_zero,
    sub_zero, neg_zero]
  rw [mul_C_eq_smul410 (A * B ^ 2) u]
  module

private theorem gamma_constant_U_delta_I1_rays410
    (gamma delta zeta eta theta u q1 : k) (A B : k[X])
    (hdelta : delta ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B (C u) = C q1) :
    A.natDegree = B.natDegree ∨
      2 * A.natDegree = 3 * B.natDegree ∨
      A.natDegree = 2 * B.natDegree := by
  rw [discriminantInvariantOne410_constant_U_decomposition] at hOne
  let s : k := 5 * u - 8 * gamma
  let P1 : k[X] := (-(320 * delta) : k) • (A ^ 2 * B)
  let P2 : k[X] := (192 * s : k) • (A * B ^ 2)
  let P3 : k[X] := (-(320 : k)) • B ^ 4
  let R : k[X] := (-(1536 * zeta) : k) • (A * B) +
    gammaConstantUI1GroundTail410 gamma delta eta theta u B
  have hP1 : P1 ≠ 0 := by
    dsimp only [P1]
    exact smul_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta))
      (mul_ne_zero (pow_ne_zero 2 hA) hB)
  have hP3 : P3 ≠ 0 := by
    dsimp only [P3]
    exact smul_ne_zero (by norm_num) (pow_ne_zero 4 hB)
  have hP1deg : P1.natDegree = 2 * A.natDegree + B.natDegree := by
    dsimp only [P1]
    rw [natDegree_smul _
        (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hdelta)),
      natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
  have hP3deg : P3.natDegree = 4 * B.natDegree := by
    dsimp only [P3]
    rw [natDegree_smul _ (by norm_num), natDegree_pow]
  by_cases hs : s = 0
  · have hsum : P1 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R, s] at hs ⊢
      simp only [hs, mul_zero, zero_smul, add_zero] at hOne
      linear_combination hOne
    have hR : R.natDegree < max P1.natDegree P3.natDegree := by
      dsimp only [R, gammaConstantUI1GroundTail410]
      rw [hP1deg, hP3deg]
      compute_degree
      omega
    have hbelow : (P1 + P3).natDegree < max P1.natDegree P3.natDegree := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hP1deg, hP3deg]; omega) hR)
    have heq := constantU_twoTerm_degree_eq410 P1 P3 hP1 hP3 hbelow
    rw [hP1deg, hP3deg] at heq
    omega
  · have hP2 : P2 ≠ 0 := by
      dsimp only [P2]
      exact smul_ne_zero (mul_ne_zero (by norm_num) hs)
        (mul_ne_zero hA (pow_ne_zero 2 hB))
    have hP2deg : P2.natDegree = A.natDegree + 2 * B.natDegree := by
      dsimp only [P2]
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hs),
        natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    have hsum : P1 + P2 + P3 = C q1 - R := by
      dsimp only [P1, P2, P3, R, s]
      linear_combination hOne
    have hR : R.natDegree <
        max P1.natDegree (max P2.natDegree P3.natDegree) := by
      dsimp only [R, gammaConstantUI1GroundTail410]
      rw [hP1deg, hP2deg, hP3deg]
      compute_degree
      omega
    have hbelow : (P1 + P2 + P3).natDegree <
        max P1.natDegree (max P2.natDegree P3.natDegree) := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hP1deg, hP2deg, hP3deg]; omega) hR)
    have htie := constantU_threeTerm_degree_tie410
      P1 P2 P3 hP1 hP2 hP3 hbelow
    rw [hP1deg, hP2deg, hP3deg] at htie
    simp only [constantUThreeTie410] at htie
    omega

private theorem gamma_constant_U_zeta_I1_rays410
    (gamma zeta eta theta u q1 : k) (A B : k[X])
    (hzeta : zeta ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hBpos : 0 < B.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma 0 zeta eta theta A B (C u) = C q1) :
    ((5 * u - 8 * gamma = 0 ∧ A.natDegree = 3 * B.natDegree) ∨
      (5 * u - 8 * gamma ≠ 0 ∧ A.natDegree = 2 * B.natDegree)) := by
  rw [discriminantInvariantOne410_constant_U_decomposition] at hOne
  simp only [mul_zero, neg_zero, zero_smul, zero_add] at hOne
  let s : k := 5 * u - 8 * gamma
  let PS : k[X] := (192 * s : k) • (A * B ^ 2)
  let PB : k[X] := (-(320 : k)) • B ^ 4
  let PZ : k[X] := (-(1536 * zeta) : k) • (A * B)
  let R : k[X] := gammaConstantUI1GroundTail410 gamma 0 eta theta u B
  have hPB : PB ≠ 0 := by
    dsimp only [PB]
    exact smul_ne_zero (by norm_num) (pow_ne_zero 4 hB)
  have hPZ : PZ ≠ 0 := by
    dsimp only [PZ]
    exact smul_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hzeta))
      (mul_ne_zero hA hB)
  have hPBdeg : PB.natDegree = 4 * B.natDegree := by
    dsimp only [PB]
    rw [natDegree_smul _ (by norm_num), natDegree_pow]
  have hPZdeg : PZ.natDegree = A.natDegree + B.natDegree := by
    dsimp only [PZ]
    rw [natDegree_smul _
        (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hzeta)),
      natDegree_mul hA hB]
  by_cases hs : s = 0
  · left
    refine ⟨by simpa only [s] using hs, ?_⟩
    have hsum : PB + PZ = C q1 - R := by
      dsimp only [PS, PB, PZ, R, s] at hs ⊢
      simp only [hs, mul_zero, zero_smul, zero_add, add_zero,
        neg_zero] at hOne
      linear_combination hOne
    have hR : R.natDegree < max PB.natDegree PZ.natDegree := by
      dsimp only [R, gammaConstantUI1GroundTail410]
      rw [hPBdeg, hPZdeg]
      compute_degree
      omega
    have hbelow : (PB + PZ).natDegree < max PB.natDegree PZ.natDegree := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hPBdeg, hPZdeg]; omega) hR)
    have heq := constantU_twoTerm_degree_eq410 PB PZ hPB hPZ hbelow
    rw [hPBdeg, hPZdeg] at heq
    omega
  · right
    refine ⟨by simpa only [s] using hs, ?_⟩
    have hPS : PS ≠ 0 := by
      dsimp only [PS]
      exact smul_ne_zero (mul_ne_zero (by norm_num) hs)
        (mul_ne_zero hA (pow_ne_zero 2 hB))
    have hPSdeg : PS.natDegree = A.natDegree + 2 * B.natDegree := by
      dsimp only [PS]
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hs),
        natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    have hsum : PS + PB + PZ = C q1 - R := by
      dsimp only [PS, PB, PZ, R, s]
      linear_combination hOne
    have hR : R.natDegree <
        max PS.natDegree (max PB.natDegree PZ.natDegree) := by
      dsimp only [R, gammaConstantUI1GroundTail410]
      rw [hPSdeg, hPBdeg, hPZdeg]
      compute_degree
      omega
    have hbelow : (PS + PB + PZ).natDegree <
        max PS.natDegree (max PB.natDegree PZ.natDegree) := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hPSdeg, hPBdeg, hPZdeg]; omega) hR)
    have htie := constantU_threeTerm_degree_tie410
      PS PB PZ hPS hPB hPZ hbelow
    rw [hPSdeg, hPBdeg, hPZdeg] at htie
    simp only [constantUThreeTie410] at htie
    omega

private theorem gamma_constant_U_base_I1_ray410
    (gamma eta theta u q1 : k) (A B : k[X])
    (hA : A ≠ 0) (hB : B ≠ 0) (hBpos : 0 < B.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma 0 0 eta theta A B (C u) = C q1) :
    5 * u - 8 * gamma ≠ 0 ∧ A.natDegree = 2 * B.natDegree := by
  rw [discriminantInvariantOne410_constant_U_decomposition] at hOne
  simp only [mul_zero, neg_zero, zero_smul, zero_add] at hOne
  let s : k := 5 * u - 8 * gamma
  let PS : k[X] := (192 * s : k) • (A * B ^ 2)
  let PB : k[X] := (-(320 : k)) • B ^ 4
  let R : k[X] := gammaConstantUI1GroundTail410 gamma 0 eta theta u B
  have hPB : PB ≠ 0 := by
    dsimp only [PB]
    exact smul_ne_zero (by norm_num) (pow_ne_zero 4 hB)
  have hPBdeg : PB.natDegree = 4 * B.natDegree := by
    dsimp only [PB]
    rw [natDegree_smul _ (by norm_num), natDegree_pow]
  by_cases hs : s = 0
  · have hform : PB + R = C q1 := by
      dsimp only [PS, PB, R, s] at hs ⊢
      simp only [hs, mul_zero, zero_smul, zero_add, add_zero,
        neg_zero] at hOne
      exact hOne
    have hR : R.natDegree < 4 * B.natDegree := by
      dsimp only [R, gammaConstantUI1GroundTail410]
      compute_degree
      omega
    exact False.elim ((smul_add_lower_ne_C410 (-(320 : k)) q1
      (B ^ 4) R (4 * B.natDegree) (by norm_num) (pow_ne_zero 4 hB)
      (by omega) (by rw [natDegree_pow]) hR) (by
        dsimp only [PB] at hform
        exact hform))
  · refine ⟨by simpa only [s] using hs, ?_⟩
    have hPS : PS ≠ 0 := by
      dsimp only [PS]
      exact smul_ne_zero (mul_ne_zero (by norm_num) hs)
        (mul_ne_zero hA (pow_ne_zero 2 hB))
    have hPSdeg : PS.natDegree = A.natDegree + 2 * B.natDegree := by
      dsimp only [PS]
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hs),
        natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
    have hsum : PS + PB = C q1 - R := by
      dsimp only [PS, PB, R, s]
      linear_combination hOne
    have hR : R.natDegree < max PS.natDegree PB.natDegree := by
      dsimp only [R, gammaConstantUI1GroundTail410]
      rw [hPSdeg, hPBdeg]
      compute_degree
      omega
    have hbelow : (PS + PB).natDegree < max PS.natDegree PB.natDegree := by
      rw [hsum]
      exact (natDegree_sub_le _ _).trans_lt
        (max_lt (by rw [natDegree_C, hPSdeg, hPBdeg]; omega) hR)
    have heq := constantU_twoTerm_degree_eq410 PS PB hPS hPB hbelow
    rw [hPSdeg, hPBdeg] at heq
    omega

def gammaConstantUDeltaFiberRest410
    (gamma delta zeta theta q2 u : k) (A B : k[X]) : k[X] :=
  (-(960 * delta) : k) • (A ^ 2 * C u) -
    (1280 * delta : k) • (A * B ^ 2) +
    (256 * (5 * u - 8 * gamma) : k) • B ^ 3 +
    (320 * delta : k) • (C u) ^ 2 +
    (1280 * zeta : k) • A ^ 3 - (3072 * zeta : k) • B ^ 2 -
    (1536 * zeta : k) • (A * C u) +
    (3072 * theta : k) • A ^ 2 - (2048 * theta : k) • C u - q2 • A

theorem gammaLaterFiberPrimitive410_constant_U_delta_decomposition
    (gamma delta zeta theta q2 u : k) (A B : k[X]) :
    gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B (C u) =
      (560 * delta : k) • A ^ 4 +
        gammaConstantUDeltaFiberRest410
          gamma delta zeta theta q2 u A B := by
  simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaConstantUDeltaFiberRest410,
    zero_mul, mul_zero, zero_smul, add_zero, sub_zero, neg_zero]
  rw [mul_C_eq_smul410 (B ^ 3) u]
  module

def gammaConstantUZetaFiberRest410
    (gamma zeta theta q2 u : k) (A B : k[X]) : k[X] :=
  (256 * (5 * u - 8 * gamma) : k) • B ^ 3 -
    (3072 * zeta : k) • B ^ 2 -
    (1536 * zeta : k) • (A * C u) + (3072 * theta : k) • A ^ 2 -
    (2048 * theta : k) • C u - q2 • A

theorem gammaLaterFiberPrimitive410_constant_U_zeta_decomposition
    (gamma zeta theta q2 u : k) (A B : k[X]) :
    gammaLaterFiberPrimitive410 gamma 0 zeta theta q2 A B (C u) =
      (1280 * zeta : k) • A ^ 3 +
        gammaConstantUZetaFiberRest410 gamma zeta theta q2 u A B := by
  simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaConstantUZetaFiberRest410,
    zero_mul, mul_zero, zero_smul, add_zero, sub_zero, neg_zero]
  rw [mul_C_eq_smul410 (B ^ 3) u]
  module

def gammaConstantUThetaFiberRest410
    (gamma theta q2 u : k) (A B : k[X]) : k[X] :=
  (256 * (5 * u - 8 * gamma) : k) • B ^ 3 -
    (2048 * theta : k) • C u - q2 • A

theorem gammaLaterFiberPrimitive410_constant_U_theta_decomposition
    (gamma theta q2 u : k) (A B : k[X]) :
    gammaLaterFiberPrimitive410 gamma 0 0 theta q2 A B (C u) =
      (3072 * theta : k) • A ^ 2 +
        gammaConstantUThetaFiberRest410 gamma theta q2 u A B := by
  simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
    deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
    deltaLaterTerminalLoadPrimitive410, gammaConstantUThetaFiberRest410,
    zero_mul, mul_zero, zero_smul, add_zero, sub_zero, neg_zero]
  rw [mul_C_eq_smul410 (B ^ 3) u]
  module

theorem gamma_nonzero_constant_U_impossible
    (gamma delta zeta eta theta q2 q1 terminal : k) (A B U : k[X])
    (hterminal : terminal ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hU0 : U.natDegree = 0) (hBpos : 0 < B.natDegree)
    (hTwo : discriminantInvariantTwoNumerator410
      0 0 gamma delta zeta eta theta A B U = C q2)
    (hOne : discriminantInvariantOneNumerator410
      0 0 gamma delta zeta eta theta A B U = C q1)
    (hTerminal : lWallTerminalNumerator410
      0 0 gamma delta zeta eta theta A B U = C terminal)
    (hfan : GammaI2FirstCompetitionExactOffTieFan410
      delta zeta eta theta A B U) : False := by
  obtain ⟨u, hu⟩ := natDegree_eq_zero.mp hU0
  subst U
  have hDerivative : derivative
      (gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B (C u)) =
        C terminal := by
    rw [← lWallTerminal410_gammaLater_eq_fiberDerivative
      gamma delta zeta eta theta q2 A B (C u) hTwo]
    exact hTerminal
  have hDegree : (gammaLaterFiberPrimitive410
      gamma delta zeta theta q2 A B (C u)).natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C410
      (gammaLaterFiberPrimitive410 gamma delta zeta theta q2 A B (C u))
      terminal hterminal hDerivative
  rcases hfan with hdelta | hzeta | htheta | hbase
  · have hrays := gamma_constant_U_delta_I1_rays410
      gamma delta zeta eta theta u q1 A B hdelta.1 hA hB hBpos hOne
    rw [gammaLaterFiberPrimitive410_constant_U_delta_decomposition] at hDegree
    have hrest : (gammaConstantUDeltaFiberRest410
        gamma delta zeta theta q2 u A B).natDegree <
          4 * A.natDegree := by
      simp only [gammaConstantUDeltaFiberRest410]
      compute_degree
      rcases hrays with hray | hray | hray <;> omega
    have hmain : ((560 * delta : k) • A ^ 4).natDegree =
        4 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hdelta.1),
        natDegree_pow]
    rw [natDegree_add_eq_left_of_natDegree_lt (by
      rw [hmain]
      exact hrest), hmain] at hDegree
    rcases hrays with hray | hray | hray <;> omega
  · have hOne0 : discriminantInvariantOneNumerator410
        0 0 gamma 0 zeta eta theta A B (C u) = C q1 := by
      simpa only [hzeta.1] using hOne
    have hrays := gamma_constant_U_zeta_I1_rays410
      gamma zeta eta theta u q1 A B hzeta.2.1 hA hB hBpos hOne0
    have hDegree0 : (gammaLaterFiberPrimitive410
        gamma 0 zeta theta q2 A B (C u)).natDegree = 1 := by
      simpa only [hzeta.1] using hDegree
    rw [gammaLaterFiberPrimitive410_constant_U_zeta_decomposition] at hDegree0
    have hrest : (gammaConstantUZetaFiberRest410
        gamma zeta theta q2 u A B).natDegree < 3 * A.natDegree := by
      simp only [gammaConstantUZetaFiberRest410]
      compute_degree
      rcases hrays with hray | hray <;> omega
    have hmain : ((1280 * zeta : k) • A ^ 3).natDegree =
        3 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hzeta.2.1),
        natDegree_pow]
    rw [natDegree_add_eq_left_of_natDegree_lt (by
      rw [hmain]
      exact hrest), hmain] at hDegree0
    rcases hrays with hray | hray <;> omega
  · have hOne0 : discriminantInvariantOneNumerator410
        0 0 gamma 0 0 eta theta A B (C u) = C q1 := by
      simpa only [htheta.1, htheta.2.1] using hOne
    have hray := gamma_constant_U_base_I1_ray410
      gamma eta theta u q1 A B hA hB hBpos hOne0
    have hDegree0 : (gammaLaterFiberPrimitive410
        gamma 0 0 theta q2 A B (C u)).natDegree = 1 := by
      simpa only [htheta.1, htheta.2.1] using hDegree
    rw [gammaLaterFiberPrimitive410_constant_U_theta_decomposition]
      at hDegree0
    have hrest : (gammaConstantUThetaFiberRest410
        gamma theta q2 u A B).natDegree < 2 * A.natDegree := by
      simp only [gammaConstantUThetaFiberRest410]
      compute_degree
      omega
    have hmain : ((3072 * theta : k) • A ^ 2).natDegree =
        2 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) htheta.2.2.1),
        natDegree_pow]
    rw [natDegree_add_eq_left_of_natDegree_lt (by
      rw [hmain]
      exact hrest), hmain] at hDegree0
    omega
  · have hOne0 : discriminantInvariantOneNumerator410
        0 0 gamma 0 0 eta 0 A B (C u) = C q1 := by
      simpa only [hbase.1, hbase.2.1, hbase.2.2.1] using hOne
    have hray := gamma_constant_U_base_I1_ray410
      gamma eta 0 u q1 A B hA hB hBpos hOne0
    have hDegree0 : (gammaLaterFiberPrimitive410
        gamma 0 0 0 q2 A B (C u)).natDegree = 1 := by
      simpa only [hbase.1, hbase.2.1, hbase.2.2.1] using hDegree
    have hform : gammaLaterFiberPrimitive410
        gamma 0 0 0 q2 A B (C u) =
          (256 * (5 * u - 8 * gamma) : k) • B ^ 3 - q2 • A := by
      simp only [gammaLaterFiberPrimitive410, gammaLaterTerminalPrimitive410,
        deltaLaterTerminalPrimitive410, deltaTerminalPrimitive410,
        deltaLaterTerminalLoadPrimitive410, zero_mul, mul_zero, zero_smul,
        add_zero, sub_zero, neg_zero]
      rw [mul_C_eq_smul410 (B ^ 3) u]
      module
    rw [hform] at hDegree0
    have hmain : ((256 * (5 * u - 8 * gamma) : k) • B ^ 3).natDegree =
        3 * B.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hray.1),
        natDegree_pow]
    have hrest : (q2 • A).natDegree < 3 * B.natDegree := by
      compute_degree
      omega
    rw [natDegree_sub_eq_left_of_natDegree_lt (by
      rw [hmain]
      exact hrest), hmain] at hDegree0
    omega

def GammaConstantBoundariesDeletedSelector410 (A B U : k[X]) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ U ≠ 0 ∧
    0 < B.natDegree ∧ 0 < U.natDegree ∧
      GammaReducedPositiveOffTieCones410 A B U

def ConstantBoundariesDeletedGammaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  DescendedCoreDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0 ∧
    GammaConstantBoundariesDeletedSelector410
      A B (A ^ 2 - (4 : k) • C0)

def ConstantBoundariesDeletedNoncubicEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0) ∧
    ConstantBoundariesDeletedGammaNewtonResidual410
      gamma delta zeta eta theta A B C0

theorem constantIntegral410_constantBoundariesDeletedNoncubic_residual
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
    l = 0 ∧ ConstantBoundariesDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_constantBDeletedNoncubic_residual
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
    hdesc, hsel.1, hsel.2.1, hsel.2.2.1, ?_⟩
  rcases hsel.2.2.2 with hU0 | hpositive
  · exact (gamma_nonzero_constant_U_impossible
      gamma delta zeta eta theta (2048 * k2) (2048 * k1)
        (8192 * terminal) A B U (mul_ne_zero (by norm_num) hterminal)
        hsel.1 hsel.2.1 hU0
        (Nat.pos_of_ne_zero (fun hB0 =>
          hdesc.1.1.1.1.1.1.1.2 ⟨hB0, hU0⟩))
        hTwoD hOneD hTerminalD hfan).elim
  · exact hpositive

theorem integrated410_constantBoundariesDeletedNoncubic_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧ ConstantBoundariesDeletedNoncubicEarlyLoadResidual410
      beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_constantBoundariesDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

theorem normalized410ScaleZero_constantBoundariesDeletedNoncubic_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X], terminal ≠ 0 ∧ l = 0 ∧
        ConstantBoundariesDeletedNoncubicEarlyLoadResidual410
          beta gamma delta zeta eta theta A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_constantBoundariesDeletedNoncubic_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end GammaConstantUAndHighBFan410

end Max11DegreeRoutes
