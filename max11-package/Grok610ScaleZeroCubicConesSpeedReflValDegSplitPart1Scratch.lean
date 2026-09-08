import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart0Scratch

/-! # SPEED: theorems of `Grok610ScaleZeroCubicConesSpeedReflValDegScratch`, part 1 of 16, so that no single
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

section CubicResidual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 32000000 in
theorem normalized610ScaleZero_cubicResidual
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
          A B C D E).natDegree =
        0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0 := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C0, D0, E0,
      ht, hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg,
      _, _, _, _, _⟩ :=
    normalized610ScaleZero_coneKappaMuResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, cubicC610 A C0,
    cubicD610 A B D0, cubicE610 A C0 E0, ht, hj, hjdiv, hHsq, ?_, ?_, ?_,
    ?_, ?_⟩
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hder
    rw [degreeZeroPrimitivePolynomial610_eq_cubic] at hder
    exact hder
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hlamDeg
    rw [degreeZeroLambdaPolynomial610_eq_cubic] at hlamDeg
    exact hlamDeg
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hkapDeg
    rw [degreeZeroKappaPolynomial610_eq_cubic] at hkapDeg
    exact hkapDeg
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at hmuDeg
    rw [degreeZeroMuPolynomial610_eq_cubic] at hmuDeg
    exact hmuDeg
  · have hC0 := (cubicC610_add A C0).symm
    have hD0 := (cubicD610_add A B D0).symm
    have hE0 := cubicE610_inv A C0 E0
    rw [hC0, hD0, hE0] at homiDeg
    rw [degreeZeroOmicronPolynomial610_eq_cubic] at homiDeg
    exact homiDeg


end CubicResidual610

section CubicDegreeHelpers610

variable {k : Type*} [Field k] [CharZero k]

theorem natDegree_pow_mul5_le610
    (A B C D E : k[X]) (ia ib ic id ie : ℕ) :
    (A ^ ia * B ^ ib * C ^ ic * D ^ id * E ^ ie).natDegree ≤
      ia * A.natDegree + ib * B.natDegree + ic * C.natDegree +
        id * D.natDegree + ie * E.natDegree := by
  have hA : (A ^ ia).natDegree ≤ ia * A.natDegree := (natDegree_pow A ia).le
  have hB : (B ^ ib).natDegree ≤ ib * B.natDegree := (natDegree_pow B ib).le
  have hC : (C ^ ic).natDegree ≤ ic * C.natDegree := (natDegree_pow C ic).le
  have hD : (D ^ id).natDegree ≤ id * D.natDegree := (natDegree_pow D id).le
  have hE : (E ^ ie).natDegree ≤ ie * E.natDegree := (natDegree_pow E ie).le
  have hAB :
      (A ^ ia * B ^ ib).natDegree ≤ ia * A.natDegree + ib * B.natDegree :=
    (natDegree_mul_le (p := A ^ ia) (q := B ^ ib)).trans (add_le_add hA hB)
  have hABC :
      (A ^ ia * B ^ ib * C ^ ic).natDegree ≤
        ia * A.natDegree + ib * B.natDegree + ic * C.natDegree :=
    (natDegree_mul_le (p := A ^ ia * B ^ ib) (q := C ^ ic)).trans
      (add_le_add hAB hC)
  have hABCD :
      (A ^ ia * B ^ ib * C ^ ic * D ^ id).natDegree ≤
        ia * A.natDegree + ib * B.natDegree + ic * C.natDegree +
          id * D.natDegree :=
    (natDegree_mul_le (p := A ^ ia * B ^ ib * C ^ ic) (q := D ^ id)).trans
      (add_le_add hABC hD)
  exact
    (natDegree_mul_le (p := A ^ ia * B ^ ib * C ^ ic * D ^ id)
        (q := E ^ ie)).trans
      (add_le_add hABCD hE)


theorem natDegree_smul_pow_mul5_le610
    (c : k) (A B C D E : k[X]) (ia ib ic id ie : ℕ) :
    (c • (A ^ ia * B ^ ib * C ^ ic * D ^ id * E ^ ie)).natDegree ≤
      ia * A.natDegree + ib * B.natDegree + ic * C.natDegree +
        id * D.natDegree + ie * E.natDegree :=
  (natDegree_smul_le610 c _).trans
    (natDegree_pow_mul5_le610 A B C D E ia ib ic id ie)


end CubicDegreeHelpers610

section CubicKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_B_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceB610 A B C D E +
        degreeZeroLambdaCubicNoB610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceB610, degreeZeroLambdaCubicNoB610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoB610` (34 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoB610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoB610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (-(5 / 27) : k), (-(5 / 27) : k),
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
      [1, 2, 1, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoB610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeB610 A B C D E) :
    (degreeZeroLambdaCubicNoB610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroLambdaCubicNoB610_eq_polyOf]
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



theorem cubicCone_B_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeB610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt⟩
    omega
  have hc : (5 / 243 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (lambdaCubicFaceB610 A B C D E).natDegree = 4 * B.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceB610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoB610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_C_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceC610 A B C D E +
        degreeZeroLambdaCubicNoC610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceC610, degreeZeroLambdaCubicNoC610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoC610` (34 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoC610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoC610 l alpha beta delta epsilon zeta eta theta A B C D E =
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
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubicNoC610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeC610 A B C D E) :
    (degreeZeroLambdaCubicNoC610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroLambdaCubicNoC610_eq_polyOf]
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



theorem cubicCone_C_impossible
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeC610 A B C D E)
    (hdeg : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt⟩
    omega
  have hc : (-(5 / 81 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (lambdaCubicFaceC610 A B C D E).natDegree = 3 * C.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, lambdaCubicFaceC610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroLambdaCubicNoC610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroLambdaCubic610_eq_C_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt⟩
  omega



set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubic610_eq_D_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      primitiveCubicFaceD610 A B C D E +
        degreeZeroPrimitiveCubicNoD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  rw [degreeZeroPrimitiveCubic610_eq_flat]
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroPrimitiveCubicFlat610, primitiveCubicFaceD610, degreeZeroPrimitiveCubicNoD610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPrimitiveCubicNoD610` (76 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveCubicNoD610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroPrimitiveCubicNoD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 2916) : k), (-(5 / 108) : k), (5 / 324 : k),
      (-(25 / 243) : k), (-(4 / 243) : k), (-(5 / 54) : k),
      (10 / 27 : k), (5 / 27 : k), (5 / 27 : k),
      (10 / 81 : k), (5 / 9 : k), (5 / 27 : k),
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
      [3, 3, 0, 0, 0], [2, 2, 0, 1, 0], [2, 1, 2, 0, 0], [1, 3, 1, 0, 0],
      [0, 5, 0, 0, 0], [2, 0, 0, 1, 1], [1, 1, 1, 0, 1], [1, 1, 0, 2, 0],
      [1, 0, 2, 1, 0], [0, 3, 0, 0, 1], [0, 2, 1, 1, 0], [0, 1, 3, 0, 0],
      [0, 0, 1, 1, 1], [7, 0, 0, 0, 0], [5, 0, 1, 0, 0], [4, 2, 0, 0, 0],
      [4, 0, 0, 0, 1], [3, 1, 0, 1, 0], [3, 0, 2, 0, 0], [2, 2, 1, 0, 0],
      [1, 4, 0, 0, 0], [2, 0, 1, 0, 1], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0],
      [1, 0, 3, 0, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0], [0, 1, 0, 1, 1],
      [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [2, 3, 0, 0, 0], [2, 1, 0, 0, 1],
      [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0], [0, 3, 1, 0, 0],
      [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0], [0, 0, 2, 1, 0],
      [6, 0, 0, 0, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 0, 2, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1]] :=
  rfl


set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveCubicNoD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeD610 A B C D E) :
    (degreeZeroPrimitiveCubicNoD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      3 * D.natDegree := by
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroPrimitiveCubicNoD610_eq_polyOf]
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



theorem cubicCone_D_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicRatioConeD610 A B C D E)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt⟩
    omega
  have hc : (-(10 / 27 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hdeg :
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ (j / t) hjdiv hder
  have hlead : (primitiveCubicFaceD610 A B C D E).natDegree = 3 * D.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, primitiveCubicFaceD610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroPrimitiveCubicNoD610_natDegree_lt l alpha beta delta epsilon
      zeta eta theta A B C D E hcone
  rw [degreeZeroPrimitiveCubic610_eq_D_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt⟩
  omega



set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_E_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicFaceE610 A B C D E +
        degreeZeroLambdaCubicNoE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroLambdaCubic610, lambdaCubicFaceE610, degreeZeroLambdaCubicNoE610]
  all_goals module


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroLambdaCubicNoE610` (34 monomials, 5 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroLambdaCubicNoE610_eq_polyOf
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27) : k),
      (-(5 / 27) : k), (-(10 / 27) : k), (-(5 / 81) : k),
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
      [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] :=
  rfl


end CubicKills610

end Max11DegreeRoutes

end
