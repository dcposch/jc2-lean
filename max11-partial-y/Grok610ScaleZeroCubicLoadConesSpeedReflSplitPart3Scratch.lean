import Grok610ScaleZeroCubicLoadConesSpeedReflSplitPart2Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicLoadConesSpeedReflScratch`, part 3 of 4, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 1000000
set_option maxRecDepth 8000000

section CubicLoadSigmaSingleMonomial610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroOmicronCubicNoSigmaBDE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hDne, hEne, heq1, heq2, hCcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieBD : 10 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * D.natDegree := heq1
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq2
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := by
    rcases hCcmp with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rw [speedRefl_degreeZeroOmicronCubicNoSigmaBDE610_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial



set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_BDE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBDE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hDne, hEne, heq1, heq2, hCcmp⟩
    exact hBne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hBne, hDne, hEne, heq1, heq2, hCcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeBDE610_specialize_theta hcone ht4
  have hc : (5 / 81 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (omicronCubicSigmaFaceBDE610 A B C D E).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    simp only [omicronCubicSigmaFaceBDE610]
    rw [natDegree_smul _ hc,
      natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroOmicronCubic610_eq_sigmaBDE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone CDE -/



set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaCDE610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroOmicronCubicNoSigmaCE610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, hEne, heq1, heq2, hBcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have htieCE : 3 * C.natDegree = 2 * E.natDegree := by omega

  rw [speedRefl_degreeZeroOmicronCubicNoSigmaCE610_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial



set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CDE_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCDE610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hdeg : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, hDne, hEne, heq1, heq2, hBcmp⟩
    exact hCne
  have hEne : E ≠ 0 := by
    rcases hcone with ⟨_, hCne, hDne, hEne, heq1, heq2, hBcmp⟩
    exact hEne
  have hb : beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeCDE610_specialize_theta hcone ht4
  have hc : (-(5 / 27 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronCubicSigmaFaceCE610 A B C D E).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [omicronCubicSigmaFaceCE610]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroOmicronCubicNoSigmaCDE610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroOmicronCubic610_eq_sigmaCE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



end CubicLoadSigmaSingleMonomial610

section CubicLoadSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroN1CubicNoSigmaCDNoL610` (44 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroN1CubicNoSigmaCDNoL610_eq_polyOf_dupfix
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroN1CubicNoSigmaCDNoL610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27) : k),
      (-(5 / 27) : k), (35 / 6912 * l : k), (-(1 / 1152 * l) : k),
      (5 / 288 * l : k), (-(1 / 96 * l) : k), (1 / 64 * l : k),
      (1 / 32 * l : k), (3 / 128 * l : k), (1 / 8 * l : k),
      (-(1 / 16 * l) : k), (-(3 / 16 * l) : k), (-(3 / 8 * l) : k),
      (-(1 / 16 * l) : k), (3 / 8 * l : k), (4 / 243 * alpha : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (7 / 6912 * beta : k), (35 / 2592 * beta : k), (-(7 / 5184 * beta) : k),
      (7 / 144 * beta : k), (-(7 / 216 * beta) : k), (7 / 432 * beta : k),
      (-(35 / 432 * beta) : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (35 / 10368 * delta : k), (5 / 144 * delta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 36 * delta) : k), (-(5 / 72 * delta) : k),
      (-(2 / 9 * epsilon) : k), (5 / 432 * zeta : k), (1 / 12 * zeta : k),
      (-(1 / 8 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1], [2, 1, 0, 1, 0],
      [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 1, 0, 1],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0]] := by
  simp only [degreeZeroN1CubicNoSigmaCDNoL610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 64000000 in
/-- Off-wall N₁ rest bound: odd pure-`A` columns are strictly below the
`C²D` face.  Band hypotheses use strict `<` so the odd pure-`A`
columns stay below the face.  At a wall `7 T = 18a` (etc.) the
corresponding column *ties* the face — those equalities are the
N₁/N₂ 2×2, not this lemma. -/
theorem degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) < 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) < 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨      12 * A.natDegree  <  6 * A.natDegree +  6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) < 54 * A.natDegree + 42 * C.natDegree) :
    (degreeZeroN1CubicNoSigmaCDNoL610 0 alpha beta delta epsilon zeta eta
        theta A B C D E).natDegree <
      2 * C.natDegree + D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hDne, heq, hBcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hCD : A.natDegree + 2 * D.natDegree = 3 * C.natDegree := by omega
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  rw [speedRefl_degreeZeroN1CubicNoSigmaCDNoL610_eq_polyOf_dupfix]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hEcmp with rfl | hEcmp <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial


set_option maxHeartbeats 64000000 in
/-- N₁ kill off the odd-column walls, on the chamber `2c+d > a`. -/
theorem cubicLoadSigmaCone_CD_offWall_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) < 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) < 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨      12 * A.natDegree  <  6 * A.natDegree +  6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) < 54 * A.natDegree + 42 * C.natDegree)
    (hTpos : A.natDegree < 2 * C.natDegree + D.natDegree)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, _⟩
    exact hCne
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, _, hDne, _⟩
    exact hDne
  have hN1le := degreeZeroN1Cubic610_natDegree_le 0 alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hrest :=
    degreeZeroN1CubicNoSigmaCDNoL610_natDegree_lt_of_loadCone alpha beta
      delta epsilon zeta eta theta A B C D E hcone hb hd hz ht
  have hfaceDeg := n1CubicSigmaFaceCD610_natDegree A B C D E hCne hDne
  have hz0 : (degreeZeroN1Cubic610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).coeff (2 * C.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hN1le.trans_lt hTpos)
  rw [degreeZeroN1Cubic610_eq_sigmaCD_add_rest,
    degreeZeroN1CubicNoSigmaCD610_eq_L_add_rest, coeff_add, coeff_add] at hz0
  have hsmall :
      (degreeZeroN1CubicNoSigmaCDNoL610 0 alpha beta delta epsilon zeta eta
          theta A B C D E).coeff (2 * C.natDegree + D.natDegree) = 0 :=
    coeff_eq_zero_of_natDegree_lt hrest
  have hL0 : (n1CubicLFace610 0 A).coeff
      (2 * C.natDegree + D.natDegree) = 0 := by
    simp only [n1CubicLFace610, mul_zero, zero_smul, coeff_zero]
  rw [hsmall, hL0, add_zero, add_zero] at hz0
  exact n1CubicSigmaFaceCD610_leading_ne A B C D E hCne hDne hz0


end CubicLoadSigmaCD610

section CubicLoadConesAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Honest leftover after the 11 single-monomial load-compete cone kills
(`B,C,D,E,BD,BE,CE,DE,BCD,BDE,CDE`).

Not closed here: the multi-monomial cones `{B,C}`, `{B,C,E}`,
`{B,C,D,E}` (File C), and `{C,D}` (N₁ odd-column walls
`7T ∈ {18a,30a,6a,54a}` and the chamber `2c+d ≤ a`, where the N₁
face does not beat `degreeZeroN1Cubic610_natDegree_le`).  Next unused
row: File C identities `cubicSigmaInner_{BC,BCE,BCDE}` plus the CD
N₁/N₂ 2×2.  No finite-root shortcut is used. -/
theorem normalized610ScaleZero_cubicResidual7
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      CubicRatioConeA610 A B C D E ∧
      cubicLoadCompetes610 A B C D E ∧
      l = 0 ∧
      (cubicKappaBetaTop610 A B C D E → beta = 0) ∧
      (cubicKappaDeltaTop610 A B C D E → delta = 0) ∧
      (cubicKappaZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1BetaTop610 A B C D E → beta = 0) ∧
      (cubicN1DeltaTop610 A B C D E → delta = 0) ∧
      (cubicN1ZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1ThetaTop610 A B C D E → theta = 0) ∧
      (beta = 0 ∨
        7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree) ∧
      (delta = 0 ∨
        7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree) ∧
      (zeta = 0 ∨
        9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
        10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree) ∧
      (theta = 0 ∨
        7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree) ∧
      (CubicLoadSigmaConeBC610 A B C D E ∨
        CubicLoadSigmaConeBCE610 A B C D E ∨
        CubicLoadSigmaConeBCDE610 A B C D E ∨
        CubicLoadSigmaConeCD610 A B C D E) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand,
      hdBand, hzBand, htBand, hexh⟩ :=
    normalized610ScaleZero_cubicResidual6 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand, hdBand,
    hzBand, htBand, ?_⟩
  cases hexh with
  | sigmaB hcone =>
    exact (cubicLoadSigmaCone_B_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hkapDeg).elim
  | sigmaC hcone =>
    exact (cubicLoadSigmaCone_C_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg hjdiv hder).elim
  | sigmaD hcone =>
    exact (cubicLoadSigmaCone_D_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg).elim
  | sigmaE hcone =>
    exact (cubicLoadSigmaCone_E_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg hjdiv hder).elim
  | sigmaBC hcone => exact Or.inl hcone
  | sigmaBD hcone =>
    exact (cubicLoadSigmaCone_BD_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg).elim
  | sigmaBE hcone =>
    exact (cubicLoadSigmaCone_BE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hlamDeg).elim
  | sigmaCD hcone => exact Or.inr (Or.inr (Or.inr hcone))
  | sigmaCE hcone =>
    exact (cubicLoadSigmaCone_CE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg hjdiv hder).elim
  | sigmaDE hcone =>
    exact (cubicLoadSigmaCone_DE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand hkapDeg).elim
  | sigmaBCD hcone =>
    exact (cubicLoadSigmaCone_BCD_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg).elim
  | sigmaBCE hcone => exact Or.inr (Or.inl hcone)
  | sigmaBDE hcone =>
    exact (cubicLoadSigmaCone_BDE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg).elim
  | sigmaCDE hcone =>
    exact (cubicLoadSigmaCone_CDE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hcone hl0 hbBand hdBand
      hzBand htBand homiDeg).elim
  | sigmaBCDE hcone => exact Or.inr (Or.inr (Or.inl hcone))
  | allZero h0 =>
    rcases h0 with ⟨hB0, hC0, hD0, hE0⟩
    exact (cubicADominant_allLettersZero_impossible (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hconeA.1 hB0 hC0
      hD0 hE0 hjdiv hder).elim


end CubicLoadConesAssembly610

end Max11DegreeRoutes

end
