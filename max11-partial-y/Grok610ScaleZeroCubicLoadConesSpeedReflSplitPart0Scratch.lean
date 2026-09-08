import Grok610ScaleZeroCubicLoadConesSpeedReflSplitBaseScratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicLoadConesSpeedReflScratch`, part 0 of 4, so that no single
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

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroKappaCubicNoSigmaB610` (30 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaCubicNoSigmaB610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaB610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27) : k), (-(5 / 27) : k), (10 / 9 : k),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l) : k),
      (1 / 16 * l : k), (-(1 / 8 * l) : k), (1 / 16 * l : k),
      (-(3 / 16 * l) : k), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha) : k), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta) : k),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta) : k),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaCubicNoSigmaB610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaB610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroKappaCubicNoSigmaB610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hsC : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := by
    rcases hCcmp with h0 | hlt
    · have : C.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsD : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := by
    rcases hDcmp with h0 | hlt
    · have : D.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  have hsE : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := by
    rcases hEcmp with h0 | hlt
    · have : E.natDegree = 0 := by simp [h0]
      omega
    · exact Nat.succ_le_of_lt hlt
  rw [speedRefl_degreeZeroKappaCubicNoSigmaB610_eq_polyOf]
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
theorem cubicLoadSigmaCone_B_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeB610 A B C D E)
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
    (hdeg : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hBne : B ≠ 0 := by
    rcases hcone with ⟨_, hBne, hCcmp, hDcmp, hEcmp⟩
    exact hBne
  have hb : beta = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree :=
    cubicLoadSigmaConeB610_specialize_theta hcone ht4
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaCubicSigmaFaceB610 A B C D E).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaCubicSigmaFaceB610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaCubicNoSigmaB610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroKappaCubic610_eq_sigmaB_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone C -/



set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoSigmaC610` (34 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoSigmaC610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaC610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(10 / 27) : k), (5 / 9 : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1],
      [0, 1, 1, 1, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  simp only [degreeZeroLambdaCubicNoSigmaC610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaC610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeC610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree)
    (hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree)
    (hz : zeta  = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree)
    (ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree)
    (hpos : 0 < 3 * C.natDegree) :
    (degreeZeroLambdaCubicNoSigmaC610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hCne, hBcmp, hDcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hsFace : 0 + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hpos

  rw [speedRefl_degreeZeroLambdaCubicNoSigmaC610_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hDcmp with rfl | hDcmp <;> rcases hEcmp with rfl | hEcmp <;>
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
theorem cubicLoadSigmaCone_C_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeC610 A B C D E)
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
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  subst hl
  have hCne : C ≠ 0 := by
    rcases hcone with ⟨_, hCne, hBcmp, hDcmp, hEcmp⟩
    exact hCne
  have hb : beta = 0 ∨ 7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree :=
    cubicLoadSigmaConeC610_specialize_theta hcone ht4
  by_cases hpos : 0 < 3 * C.natDegree
  ·
      have hc : (-(5 / 81 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
      have hlead : (lambdaCubicSigmaFaceC610 A B C D E).natDegree = 3 * C.natDegree := by
        simp only [lambdaCubicSigmaFaceC610]
        rw [natDegree_smul _ hc, natDegree_pow]
      have hrest := degreeZeroLambdaCubicNoSigmaC610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
          A B C D E hcone hb hd hz ht hpos
      rw [degreeZeroLambdaCubic610_eq_sigmaC_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
      omega
  ·
    have hface0 : 3 * C.natDegree = 0 := by omega
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
      hCne, hBcmp, hDcmp, hEcmp⟩
    have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
    have hCdeg0 : C.natDegree = 0 := by omega
    have hB0 : B = 0 := by
      rcases hBcmp with hB0 | hBlt
      · exact hB0
      · omega
    have hD0 : D = 0 := by
      rcases hDcmp with hD0 | hDlt
      · exact hD0
      · omega
    rw [hCdeg0] at hb hd hz ht
    have hbeta0 : beta = 0 := by
      rcases hb with h | h
      · exact h
      · omega
    have hdelta0 : delta = 0 := by
      rcases hd with h | h
      · exact h
      · omega
    have hzeta0 : zeta = 0 := by
      rcases hz with h | h
      · exact h
      · omega
    have htheta0 : theta = 0 := by
      rcases ht with h | h
      · exact h
      · omega
    exact cubicLoadCompete_BD_zero_impossible (j := j) (t := t)
      0 alpha beta delta epsilon zeta eta theta A B C D E
      hB0 hD0 rfl hbeta0 hdelta0 hzeta0 htheta0 hjdiv hder



/- σ-cone D -/



set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoSigmaD610` (34 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoSigmaD610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(10 / 27) : k), (-(5 / 81) : k), (5 / 9 : k),
      (-(5 / 6912 * l) : k), (-(1 / 288 * l) : k), (-(1 / 96 * l) : k),
      (1 / 32 * l : k), (-(1 / 8 * l) : k), (-(1 / 8 * l) : k),
      (-(3 / 16 * l) : k), (-(3 / 16 * l) : k), (3 / 4 * l : k),
      (-(4 / 27 * alpha) : k), (-(4 / 27 * alpha) : k), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta) : k), (-(7 / 432 * beta) : k),
      (-(7 / 216 * beta) : k), (-(35 / 1296 * beta) : k), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta) : k), (-(5 / 36 * delta) : k),
      (-(5 / 36 * delta) : k), (-(1 / 9 * epsilon) : k), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta) : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  simp only [degreeZeroLambdaCubicNoSigmaD610, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaD610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeD610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree)
    (hd : delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree)
    (hz : zeta  = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree)
    (ht : theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree) :
    (degreeZeroLambdaCubicNoSigmaD610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hDne, hBcmp, hCcmp, hEcmp⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)

  rw [speedRefl_degreeZeroLambdaCubicNoSigmaD610_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hBcmp with rfl | hBcmp <;> rcases hCcmp with rfl | hCcmp <;> rcases hEcmp with rfl | hEcmp <;>
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
theorem cubicLoadSigmaCone_D_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeD610 A B C D E)
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
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0) :
    False := by
  subst hl
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩, _⟩
    omega
  have hDne : D ≠ 0 := by
    rcases hcone with ⟨_, hDne, hBcmp, hCcmp, hEcmp⟩
    exact hDne
  have hb : beta = 0 ∨ 7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_beta hcone hb4
  have hd : delta = 0 ∨ 7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_delta hcone hd4
  have hz : zeta = 0 ∨ 10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_zeta hcone hz4
  have ht : theta = 0 ∨ 7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree :=
    cubicLoadSigmaConeD610_specialize_theta hcone ht4
  have hc : (-(5 / 27 : k)) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicSigmaFaceD610 A B C D E).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [lambdaCubicSigmaFaceD610]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoSigmaD610_natDegree_lt_of_loadCone alpha beta delta epsilon zeta eta theta
      A B C D E hcone hb hd hz ht
  rw [degreeZeroLambdaCubic610_eq_sigmaD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega



/- σ-cone E -/



end CubicLoadSigmaSingleMonomial610

end Max11DegreeRoutes

end
