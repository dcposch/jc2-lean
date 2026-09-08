import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart12Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 13 of 16, so that no single
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

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPrimitiveCubicNoABDE610` (70 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveCubicNoABDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroPrimitiveCubicNoABDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 324 : k), (-(25 / 243) : k), (10 / 27 : k),
      (5 / 27 : k), (5 / 9 : k), (5 / 27 : k),
      (-(10 / 9) : k), (5 / 27648 * l : k), (25 / 6912 * l : k),
      (-(17 / 13824 * l) : k), (1 / 128 * l : k), (1 / 288 * l : k),
      (13 / 576 * l : k), (-(5 / 192 * l) : k), (-(1 / 32 * l) : k),
      (1 / 16 * l : k), (1 / 8 * l : k), (3 / 8 * l : k),
      (1 / 16 * l : k), (3 / 16 * l : k), (9 / 32 * l : k),
      (-(3 / 4 * l) : k), (-(3 / 8 * l) : k), (-(3 / 4 * l) : k),
      (-(1 / 81 * alpha) : k), (-(1 / 27 * alpha) : k), (-(1 / 27 * alpha) : k),
      (4 / 27 * alpha : k), (4 / 27 * alpha : k), (4 / 27 * alpha : k),
      (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k), (-(4 / 9 * alpha) : k),
      (-(4 / 9 * alpha) : k), (35 / 62208 * beta : k), (49 / 5184 * beta : k),
      (-(7 / 1728 * beta) : k), (7 / 432 * beta : k), (-(7 / 216 * beta) : k),
      (7 / 144 * beta : k), (35 / 432 * beta : k), (35 / 1728 * beta : k),
      (7 / 36 * beta : k), (-(7 / 36 * beta) : k), (-(7 / 72 * beta) : k),
      (-(7 / 18 * beta) : k), (-(7 / 108 * beta) : k), (7 / 12 * beta : k),
      (1 / 576 * delta : k), (5 / 216 * delta : k), (-(5 / 216 * delta) : k),
      (5 / 36 * delta : k), (5 / 36 * delta : k), (-(5 / 12 * delta) : k),
      (-(1 / 18 * epsilon) : k), (2 / 9 * epsilon : k), (2 / 27 * epsilon : k),
      (-(2 / 3 * epsilon) : k), (1 / 192 * zeta : k), (1 / 24 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 2 * zeta) : k), (-(1 / 4 * zeta) : k),
      (-(1 / 36 * eta) : k), (-(1 / 3 * eta) : k), (-(1 / 3 * eta) : k),
      (1 / 72 * theta : k), (1 / 6 * theta : k), (-(1 / 12 * theta) : k),
      (1 * theta : k)]
      [
      [2, 1, 2, 0, 0], [1, 3, 1, 0, 0], [1, 1, 1, 0, 1], [1, 0, 2, 1, 0],
      [0, 2, 1, 1, 0], [0, 1, 3, 0, 0], [0, 0, 1, 1, 1], [7, 0, 0, 0, 0],
      [5, 0, 1, 0, 0], [4, 2, 0, 0, 0], [4, 0, 0, 0, 1], [3, 1, 0, 1, 0],
      [3, 0, 2, 0, 0], [2, 2, 1, 0, 0], [1, 4, 0, 0, 0], [2, 0, 1, 0, 1],
      [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [1, 0, 3, 0, 0], [0, 3, 0, 1, 0],
      [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0],
      [2, 3, 0, 0, 0], [2, 1, 0, 0, 1], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [6, 0, 0, 0, 0], [4, 0, 1, 0, 0],
      [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0], [2, 0, 2, 0, 0],
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 0, 2, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveCubicNoABDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E) :
    (degreeZeroPrimitiveCubicNoABDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  rw [speedRefl_degreeZeroPrimitiveCubicNoABDE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem primitiveCubicFaceABDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (primitiveCubicFaceABDE610 A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) =
      (1 / 2916 : k) * primitiveCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, primitiveCubicFaceABDE610, primitiveCubicInnerABDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3B3 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A3B3 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A3B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2D : ((A ^ 2 * B ^ 2 * D)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2D : ((A ^ 2 * B ^ 2 * D)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DE : ((A ^ 2 * D * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DE : ((A ^ 2 * D * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABD2 : ((A * B * D ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hDne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABD2 : ((A * B * D ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ABD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B5 : (B ^ 5).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_B5 : (B ^ 5).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B3E : ((B ^ 3 * E)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hEne, natDegree_pow]
    omega
  have hcf_B3E : ((B ^ 3 * E)).coeff (3 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_B3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D3 : (D ^ 3).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_D3 : (D ^ 3).coeff (3 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 3 := by
    rw [← hdeg_D3, coeff_natDegree, leadingCoeff_pow]
  simp only [← mul_assoc]
  rw [hcf_A3B3, hcf_A2B2D, hcf_A2DE, hcf_ABD2, hcf_B5, hcf_B3E, hcf_D3]
  ring


set_option maxHeartbeats 64000000 in
theorem cubicCone_ABDE_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeABDE610 A B C D E)
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree =
        0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hkappainner : kappaCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := kappaCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroKappaCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hlambdainner : lambdaCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroLambdaCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := lambdaCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hlam]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroLambdaCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 243 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroMuCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := muCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroMuCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 1458 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := omicronCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroOmicronCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 486 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveCubicInnerABDE610 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveCubicNoABDE610_natDegree_lt l alpha beta delta
        epsilon zeta eta theta A B C D E hcone
    have hct := primitiveCubicFaceABDE610_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne)
    have hz : (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hAB, hAD, hAE, hClt⟩
      omega
    rw [degreeZeroPrimitiveCubic610_eq_ABDE_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2916 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := cubicInner_ABDE_identity A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff
  have hpow : D.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hlambdainner, hmuinner, homicroninner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 64000000 in
theorem cubicInner_BCDE_identity
    (b c d e : k) :
    ((-437 / 48195 : k) * b ^ 3 * c * e + (79 / 27540 : k) * b ^ 3 * d ^ 2 + (-139 / 3060 : k) * b ^ 2 * c ^ 2 * d + (-91 / 9180 : k) * b * c ^ 4 + (6733 / 64260 : k) * b * c * e ^ 2 + (-1 / 21420 : k) * b * d ^ 2 * e + (-8 / 1071 : k) * c ^ 2 * d * e + (1 / 510 : k) * c * d ^ 3) * kappaCubicInnerBCDE610 b c d e +
      ((-2 / 8505 : k) * b ^ 4 * e + (1 / 405 : k) * b ^ 2 * e ^ 2 + (-517 / 96390 : k) * b * c * d * e + (79 / 27540 : k) * b * d ^ 3 + (91 / 13770 : k) * c ^ 3 * e + (73 / 9180 : k) * c ^ 2 * d ^ 2 + (1 / 135 : k) * e ^ 3) * lambdaCubicInnerBCDE610 b c d e +
      ((-331 / 96390 : k) * b * c ^ 2 * e + (-41 / 6885 : k) * b * c * d ^ 2 + (-37 / 82620 : k) * c ^ 3 * d + (41 / 192780 : k) * d * e ^ 2) * muCubicInnerBCDE610 b c d e +
      ((-49 / 9180 : k) * b * c ^ 2 * d + (-91 / 82620 : k) * c ^ 4 + (239 / 27540 : k) * c * e ^ 2 + (1 / 1530 : k) * d ^ 2 * e) * omicronCubicInnerBCDE610 b c d e +
      ((-1 / 3402 : k) * b ^ 3 * e + (2 / 567 : k) * b * e ^ 2) * primitiveCubicInnerBCDE610 b c d e =
      e ^ 5 := by
  simp only [kappaCubicInnerBCDE610, lambdaCubicInnerBCDE610, muCubicInnerBCDE610, omicronCubicInnerBCDE610, primitiveCubicInnerBCDE610]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicFaceBCDE610 A B C D E +
        degreeZeroKappaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaCubic610, kappaCubicFaceBCDE610, degreeZeroKappaCubicNoBCDE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaCubicNoBCDE610` (28 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoBCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (7 / 6912 * l : k), (5 / 288 * l : k),
      (-(1 / 192 * l) : k), (1 / 16 * l : k), (-(1 / 8 * l) : k),
      (1 / 16 * l : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (3 / 8 * l : k), (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k),
      (4 / 9 * alpha : k), (35 / 10368 * beta : k), (7 / 144 * beta : k),
      (-(7 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (5 / 432 * delta : k), (5 / 36 * delta : k),
      (-(5 / 72 * delta) : k), (5 / 6 * delta : k), (2 / 3 * epsilon : k),
      (1 / 24 * zeta : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 3, 0, 0, 0], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
      [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroKappaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  rw [speedRefl_degreeZeroKappaCubicNoBCDE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem kappaCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (kappaCubicFaceBCDE610 A B C D E).coeff (2 * B.natDegree + D.natDegree) =
      (1 / 27 : k) * kappaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, kappaCubicFaceBCDE610, kappaCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B2D : ((B ^ 2 * D)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hcf_B2D : ((B ^ 2 * D)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (2 * B.natDegree + D.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE : ((D * E)).natDegree = 2 * B.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hEne]
    omega
  have hcf_DE : ((D * E)).coeff (2 * B.natDegree + D.natDegree) =
      D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_DE, coeff_natDegree, leadingCoeff_mul]
  rw [hcf_B2D, hcf_BC2, hcf_DE]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceBCDE610 A B C D E +
        degreeZeroLambdaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceBCDE610, degreeZeroLambdaCubicNoBCDE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoBCDE610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoBCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (-(5 / 27) : k), (-(5 / 6912 * l) : k),
      (-(1 / 288 * l) : k), (-(1 / 96 * l) : k), (1 / 32 * l : k),
      (-(1 / 8 * l) : k), (-(1 / 8 * l) : k), (-(3 / 16 * l) : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (-(4 / 27 * alpha) : k),
      (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k), (-(7 / 216 * beta) : k),
      (-(35 / 1296 * beta) : k), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k), (-(5 / 36 * delta) : k),
      (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k), (-(1 / 12 * zeta) : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroLambdaCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  rw [speedRefl_degreeZeroLambdaCubicNoBCDE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem lambdaCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicFaceBCDE610 A B C D E).coeff (4 * B.natDegree) =
      (1 / 243 : k) * lambdaCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceBCDE610, lambdaCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B4 : (B ^ 4).natDegree = 4 * B.natDegree := by
    exact natDegree_pow _ _
  have hcf_B4 : (B ^ 4).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 4 := by
    rw [← hdeg_B4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_B2E : ((B ^ 2 * E)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hEne, natDegree_pow]
    omega
  have hcf_B2E : ((B ^ 2 * E)).coeff (4 * B.natDegree) =
      B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_B2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD : ((B * C * D)).natDegree = 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hDne, natDegree_mul hBne hCne]
    omega
  have hcf_BCD : ((B * C * D)).coeff (4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_BCD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3 : (C ^ 3).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (4 * B.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (4 * B.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  simp only [← mul_assoc]
  rw [hcf_B4, hcf_B2E, hcf_BCD, hcf_C3, hcf_E2]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      muCubicFaceBCDE610 A B C D E +
        degreeZeroMuCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuCubic610, muCubicFaceBCDE610, degreeZeroMuCubicNoBCDE610]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuCubicNoBCDE610` (44 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuCubicNoBCDE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroMuCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 1458) : k), (5 / 54 : k), (5 / 162 : k),
      (-(5 / 27) : k), (35 / 248832 * l : k), (5 / 2304 * l : k),
      (1 / 144 * l : k), (1 / 96 * l : k), (1 / 192 * l : k),
      (1 / 16 * l : k), (3 / 128 * l : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 8 * l) : k), (-(1 / 16 * l) : k),
      (3 / 8 * l : k), (2 / 81 * alpha : k), (-(2 / 27 * alpha) : k),
      (-(2 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k),
      (4 / 9 * alpha : k), (7 / 15552 * beta : k), (7 / 1296 * beta : k),
      (7 / 5184 * beta : k), (7 / 432 * beta : k), (-(7 / 108 * beta) : k),
      (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 3456 * delta : k), (5 / 432 * delta : k), (5 / 216 * delta : k),
      (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k), (-(1 / 9 * epsilon) : k),
      (-(2 / 9 * epsilon) : k), (1 / 216 * zeta : k), (-(1 / 8 * zeta) : k),
      (1 / 2 * zeta : k), (-(1 / 18 * eta) : k), (1 / 3 * eta : k),
      (1 / 72 * theta : k), (1 / 6 * theta : k)]
      [
      [2, 3, 0, 0, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [1, 0, 0, 1, 1],
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] :=
  rfl


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuCubicNoBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeBCDE610 A B C D E) :
    (degreeZeroMuCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  rw [speedRefl_degreeZeroMuCubicNoBCDE610_eq_polyOf]
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
set_option maxHeartbeats 64000000 in


theorem muCubicFaceBCDE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicRatioConeBCDE610 A B C D E)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    : (muCubicFaceBCDE610 A B C D E).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 243 : k) * muCubicInnerBCDE610 B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hEpos, hBC, hBD, hBE, hAlt⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muCubicFaceBCDE610, muCubicInnerBCDE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCE : ((B * C * E)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hEne, natDegree_mul hBne hCne]
    omega
  have hcf_BCE : ((B * C * E)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (3 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  simp only [← mul_assoc]
  rw [hcf_B3C, hcf_BCE, hcf_BD2, hcf_C2D]
  ring


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubic610_eq_BCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicFaceBCDE610 A B C D E +
        degreeZeroOmicronCubicNoBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroOmicronCubic610, omicronCubicFaceBCDE610, degreeZeroOmicronCubicNoBCDE610]
  all_goals module


end CubicKills610

end Max11DegreeRoutes

end
