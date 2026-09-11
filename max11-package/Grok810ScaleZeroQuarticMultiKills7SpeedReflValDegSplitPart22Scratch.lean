import Grok810ScaleZeroQuarticDefsScratch
import Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegSplitBaseScratch

/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 22 of 24, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuartic810_eq_BCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceBCDEFG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoBCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceBCDEFG810, degreeZeroPrimitiveQuarticNoBCDEFG810]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPrimitiveQuarticNoBCDEFG810` (146 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveQuarticNoBCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuarticNoBCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(15 / 16384) : k), (15 / 16384 : k),
      (15 / 8192 : k), (65 / 8192 : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (-(5 / 2048) : k), (-(5 / 2048) : k),
      (15 / 1024 : k), (-(25 / 2048) : k), (15 / 2048 : k),
      (-(25 / 512) : k), (-(135 / 1024) : k), (-(15 / 1024) : k),
      (-(5 / 256) : k), (-(5 / 256) : k), (5 / 128 : k),
      (5 / 32 : k), (5 / 64 : k), (15 / 128 : k),
      (5 / 128 : k), (-(5 / 16) : k), (1575 / 268435456 * l : k),
      (765 / 4194304 * l : k), (-(369 / 4194304 * l) : k), (171 / 262144 * l : k),
      (-(153 / 262144 * l) : k), (855 / 524288 * l : k), (-(81 / 131072 * l) : k),
      (261 / 262144 * l : k), (45 / 32768 * l : k), (-(9 / 4096 * l) : k),
      (99 / 8192 * l : k), (-(9 / 4096 * l) : k), (-(9 / 4096 * l) : k),
      (9 / 8192 * l : k), (27 / 16384 * l : k), (-(243 / 8192 * l) : k),
      (-(387 / 16384 * l) : k), (-(567 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (27 / 1024 * l : k), (9 / 1024 * l : k),
      (9 / 256 * l : k), (45 / 512 * l : k), (9 / 1024 * l : k),
      (9 / 256 * l : k), (27 / 512 * l : k), (45 / 256 * l : k),
      (45 / 512 * l : k), (189 / 1024 * l : k), (63 / 4096 * l : k),
      (9 / 64 * l : k), (-(9 / 64 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(9 / 128 * l) : k), (-(9 / 32 * l) : k),
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k), (9 / 16 * l : k),
      (25 / 1048576 * beta : k), (21 / 32768 * beta : k), (-(119 / 262144 * beta) : k),
      (35 / 16384 * beta : k), (-(7 / 2048 * beta) : k), (21 / 4096 * beta : k),
      (-(21 / 8192 * beta) : k), (119 / 16384 * beta : k), (21 / 512 * beta : k),
      (-(7 / 512 * beta) : k), (-(21 / 512 * beta) : k), (-(7 / 128 * beta) : k),
      (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k), (7 / 64 * beta : k),
      (7 / 32 * beta : k), (7 / 32 * beta : k), (7 / 64 * beta : k),
      (7 / 64 * beta : k), (-(7 / 16 * beta) : k), (3 / 2048 * gamma : k),
      (3 / 2048 * gamma : k), (-(3 / 512 * gamma) : k), (3 / 256 * gamma : k),
      (3 / 256 * gamma : k), (-(9 / 128 * gamma) : k), (-(3 / 128 * gamma) : k),
      (-(27 / 256 * gamma) : k), (-(3 / 32 * gamma) : k), (3 / 16 * gamma : k),
      (9 / 64 * gamma : k), (3 / 8 * gamma : k), (3 / 16 * gamma : k),
      (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k), (25 / 262144 * delta : k),
      (35 / 16384 * delta : k), (-(25 / 16384 * delta) : k), (5 / 1024 * delta : k),
      (-(5 / 512 * delta) : k), (15 / 1024 * delta : k), (-(65 / 1024 * delta) : k),
      (-(135 / 4096 * delta) : k), (5 / 64 * delta : k), (5 / 64 * delta : k),
      (25 / 128 * delta : k), (15 / 32 * delta : k), (5 / 64 * delta : k),
      (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k), (-(1 / 256 * epsilon) : k),
      (1 / 64 * epsilon : k), (-(1 / 32 * epsilon) : k), (-(1 / 32 * epsilon) : k),
      (1 / 8 * epsilon : k), (1 / 16 * epsilon : k), (7 / 32 * epsilon : k),
      (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k), (-(1 / 2 * epsilon) : k),
      (3 / 8192 * zeta : k), (3 / 512 * zeta : k), (-(3 / 2048 * zeta) : k),
      (3 / 128 * zeta : k), (3 / 32 * zeta : k), (27 / 128 * zeta : k),
      (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k),
      (-(1 / 512 * eta) : k), (-(1 / 64 * eta) : k), (1 / 32 * eta : k),
      (3 / 64 * eta : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k),
      (-(1 / 4 * eta) : k), (5 / 4096 * theta : k), (3 / 128 * theta : k),
      (1 / 128 * theta : k), (1 / 8 * theta : k), (-(1 / 8 * theta) : k),
      (-(1 / 16 * theta) : k), (1 * theta : k)]
      [
      [4, 3, 0, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0],
      [1, 5, 0, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0, 1], [3, 0, 1, 0, 0, 1, 0], [3, 0, 0, 1, 1, 0, 0],
      [2, 2, 0, 0, 0, 1, 0], [2, 1, 1, 0, 1, 0, 0], [2, 1, 0, 2, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0],
      [1, 3, 0, 0, 1, 0, 0], [1, 2, 1, 1, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 1],
      [2, 0, 0, 0, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 2, 0, 0],
      [1, 0, 1, 1, 1, 0, 0], [1, 0, 0, 3, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1], [8, 0, 0, 0, 0, 0, 0],
      [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0], [4, 1, 0, 1, 0, 0, 0],
      [4, 0, 2, 0, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1],
      [3, 1, 0, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0],
      [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0],
      [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0], [2, 0, 0, 0, 2, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0],
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2], [7, 0, 0, 0, 0, 0, 0],
      [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0],
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [3, 1, 1, 0, 0, 0, 0],
      [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0],
      [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0],
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuarticNoBCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCDEFG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoBCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hBC, hBD, hBE, hBF, hBG, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  rw [speedRefl_degreeZeroPrimitiveQuarticNoBCDEFG810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial


theorem primitiveQuarticFaceBCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCDEFG810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceBCDEFG810 A B C D E F G).coeff (4 * B.natDegree + D.natDegree) =
      (1 / 2048 : k) * primitiveQuarticInnerBCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hBC, hBD, hBE, hBF, hBG, hAlt⟩
  simp only [primitiveQuarticFaceBCDEFG810, primitiveQuarticInnerBCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C2 : ((B ^ 3 * C ^ 2)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B3C2 : ((B ^ 3 * C ^ 2)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CF : ((B ^ 2 * C * F)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    omega
  have hcf_B2CF : ((B ^ 2 * C * F)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_B2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2E : ((B * C ^ 2 * E)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hEne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2E : ((B * C ^ 2 * E)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_BC2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD2 : ((B * C * D ^ 2)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) (pow_ne_zero 2 hDne), natDegree_mul hBne hCne, natDegree_pow]
    omega
  have hcf_BCD2 : ((B * C * D ^ 2)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BCD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEG : ((B * E * G)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hGne, natDegree_mul hBne hEne]
    omega
  have hcf_BEG : ((B * E * G)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff * E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BEG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BF2 : ((B * F ^ 2)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_BF2 : ((B * F ^ 2)).coeff (4 * B.natDegree + D.natDegree) =
      B.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_BF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (4 * B.natDegree + D.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (4 * B.natDegree + D.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CEF : ((C * E * F)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hEne) hFne, natDegree_mul hCne hEne]
    omega
  have hcf_CEF : ((C * E * F)).coeff (4 * B.natDegree + D.natDegree) =
      C.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (4 * B.natDegree + D.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B4D, hcf_B3C2, hcf_B3G, hcf_B2CF, hcf_B2DE, hcf_BC2E, hcf_BCD2, hcf_BEG, hcf_BF2, hcf_C3D, hcf_CDG, hcf_CEF, hcf_D2F, hcf_DE2]
  ring


end QuarticKills810

end Max11DegreeRoutes

end
