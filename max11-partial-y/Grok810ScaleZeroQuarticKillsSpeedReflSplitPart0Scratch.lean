import Grok810ScaleZeroQuarticKillsSpeedReflSplitBaseScratch

/-! # SPEED: theorems of `Grok810ScaleZeroQuarticKillsSpeedReflScratch`, part 0 of 4, so that no single
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

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoB810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoB810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoB810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (-(5 / 64) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoB810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoB810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeB810 A B C D E F G) :
    (degreeZeroMuQuarticNoB810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoB810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_B_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeB810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (35 / 2048 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceB810 A B C D E F G).natDegree = 4 * B.natDegree := by
    simp only [muQuarticFaceB810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoB810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_B_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hAlt, hClt, hDlt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoC810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoC810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoC810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoC810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeC810 A B C D E F G) :
    (degreeZeroMuQuarticNoC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoC810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_C_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeC810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceC810 A B C D E F G).natDegree = 3 * C.natDegree := by
    simp only [muQuarticFaceC810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_C_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hAlt, hBlt, hDlt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroOmicronQuarticNoD810` (101 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroOmicronQuarticNoD810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroOmicronQuarticNoD810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(45 / 16384) : k), (15 / 16384 : k),
      (-(35 / 2048) : k), (-(21 / 4096) : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (-(5 / 2048) : k), (25 / 1024 : k),
      (15 / 512 : k), (35 / 1024 : k), (15 / 1024 : k),
      (5 / 128 : k), (135 / 1024 : k), (45 / 1024 : k),
      (-(5 / 128) : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(5 / 32) : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (5 / 16 : k), (135 / 33554432 * l : k),
      (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k), (81 / 262144 * l : k),
      (-(9 / 65536 * l) : k), (99 / 131072 * l : k), (-(45 / 131072 * l) : k),
      (-(189 / 65536 * l) : k), (9 / 8192 * l : k), (-(9 / 4096 * l) : k),
      (27 / 8192 * l : k), (45 / 4096 * l : k), (99 / 4096 * l : k),
      (9 / 8192 * l : k), (189 / 8192 * l : k), (567 / 16384 * l : k),
      (9 / 512 * l : k), (-(9 / 256 * l) : k), (-(27 / 1024 * l) : k),
      (-(9 / 128 * l) : k), (-(45 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 512 * l) : k), (9 / 64 * l : k), (9 / 128 * l : k),
      (35 / 2097152 * beta : k), (49 / 131072 * beta : k), (-(35 / 131072 * beta) : k),
      (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k), (21 / 8192 * beta : k),
      (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k), (7 / 512 * beta : k),
      (7 / 512 * beta : k), (35 / 1024 * beta : k), (21 / 256 * beta : k),
      (7 / 512 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k), (-(3 / 512 * gamma) : k),
      (3 / 128 * gamma : k), (3 / 128 * gamma : k), (9 / 128 * gamma : k),
      (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k),
      (9 / 131072 * delta : k), (5 / 4096 * delta : k), (-(5 / 4096 * delta) : k),
      (5 / 128 * delta : k), (5 / 512 * delta : k), (45 / 512 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k),
      (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k), (1 / 32 * epsilon : k),
      (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k),
      (9 / 32768 * zeta : k), (3 / 1024 * zeta : k), (9 / 512 * zeta : k),
      (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k), (-(3 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 1024 * theta : k), (1 / 64 * theta : k),
      (-(3 / 128 * theta) : k), (1 / 8 * theta : k)]
      [
      [3, 3, 0, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1],
      [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1], [7, 0, 0, 0, 0, 0, 0],
      [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0],
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0],
      [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0],
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0]] := by
  simp only [degreeZeroOmicronQuarticNoD810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronQuarticNoD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeD810 A B C D E F G) :
    (degreeZeroOmicronQuarticNoD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * D.natDegree := by
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt, hFlt, hGlt⟩
  have hA1 : 5 * A.natDegree + 1 ≤ 2 * D.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 5 * B.natDegree + 1 ≤ 3 * D.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 5 * C.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : 5 * E.natDegree + 1 ≤ 6 * D.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 5 * F.natDegree + 1 ≤ 7 * D.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 5 * G.natDegree + 1 ≤ 8 * D.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroOmicronQuarticNoD810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_D_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeD810 A B C D E F G)
    (hdeg : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (omicronQuarticFaceD810 A B C D E F G).natDegree = 3 * D.natDegree := by
    simp only [omicronQuarticFaceD810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroOmicronQuarticNoD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroOmicronQuartic810_eq_D_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hDpos, hAlt, hBlt, hClt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoE810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoE810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoE810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(5 / 128) : k), (5 / 16 : k), (5 / 16 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoE810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeE810 A B C D E F G) :
    (degreeZeroMuQuarticNoE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 2 * B.natDegree + 1 ≤ E.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 3 * C.natDegree + 1 ≤ 2 * E.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 6 * D.natDegree + 1 ≤ 5 * E.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 6 * F.natDegree + 1 ≤ 7 * E.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 4 * E.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoE810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_E_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeE810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceE810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceE810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_E_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hEpos, hAlt, hBlt, hClt, hDlt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiQuarticNoF810` (60 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (-(45 / 262144 * l) : k), (9 / 16384 * l : k), (-(9 / 16384 * l) : k),
      (-(9 / 8192 * l) : k), (9 / 4096 * l : k), (-(9 / 8192 * l) : k),
      (171 / 8192 * l : k), (9 / 1024 * l : k), (63 / 2048 * l : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 256 * l) : k), (-(27 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (7 / 2048 * beta : k), (-(7 / 1024 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 256 * beta : k), (7 / 512 * beta : k), (49 / 1024 * beta : k),
      (7 / 128 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 64 * gamma : k), (3 / 32 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (-(5 / 1024 * delta) : k),
      (5 / 128 * delta : k), (5 / 128 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 64 * delta) : k), (1 / 32 * epsilon : k),
      (-(3 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 16 * eta) : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0],
      [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiQuarticNoF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuarticNoF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeF810 A B C D E F G) :
    (degreeZeroXiQuarticNoF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hFpos, hAlt, hBlt, hClt, hDlt, hElt, hGlt⟩
  have hA1 : 7 * A.natDegree + 1 ≤ 2 * F.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 7 * B.natDegree + 1 ≤ 3 * F.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 7 * C.natDegree + 1 ≤ 4 * F.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 7 * D.natDegree + 1 ≤ 5 * F.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 7 * E.natDegree + 1 ≤ 6 * F.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : 7 * G.natDegree + 1 ≤ 8 * F.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroXiQuarticNoF810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_F_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeF810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hFpos, hAlt, hBlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceF810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_F_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hFpos, hAlt, hBlt, hClt, hDlt, hElt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPiQuarticNoG810` (94 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (-(15 / 16) : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k), (45 / 131072 * l : k),
      (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k), (9 / 4096 * l : k),
      (9 / 4096 * l : k), (-(27 / 4096 * l) : k), (9 / 4096 * l : k),
      (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k), (-(27 / 1024 * l) : k),
      (9 / 512 * l : k), (63 / 1024 * l : k), (9 / 128 * l : k),
      (27 / 256 * l : k), (9 / 256 * l : k), (63 / 512 * l : k),
      (189 / 512 * l : k), (63 / 512 * l : k), (-(9 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(27 / 64 * l) : k), (-(9 / 32 * l) : k),
      (-(27 / 128 * l) : k), (-(9 / 16 * l) : k), (-(3 / 32 * l) : k),
      (9 / 8 * l : k), (7 / 4096 * beta : k), (7 / 4096 * beta : k),
      (-(7 / 1024 * beta) : k), (7 / 512 * beta : k), (7 / 512 * beta : k),
      (-(21 / 256 * beta) : k), (-(7 / 256 * beta) : k), (-(63 / 512 * beta) : k),
      (-(7 / 64 * beta) : k), (7 / 32 * beta : k), (21 / 128 * beta : k),
      (7 / 16 * beta : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (-(7 / 8 * beta) : k), (-(3 / 32 * gamma) : k), (-(15 / 256 * gamma) : k),
      (3 / 16 * gamma : k), (3 / 8 * gamma : k), (3 / 4 * gamma : k),
      (1 / 8 * gamma : k), (-(3 / 4 * gamma) : k), (-(3 / 4 * gamma) : k),
      (5 / 512 * delta : k), (-(15 / 256 * delta) : k), (-(5 / 128 * delta) : k),
      (5 / 32 * delta : k), (5 / 32 * delta : k), (15 / 32 * delta : k),
      (15 / 32 * delta : k), (-(5 / 8 * delta) : k), (-(5 / 4 * delta) : k),
      (1 / 4 * epsilon : k), (1 / 2 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k), (3 / 32 * zeta : k),
      (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 4 * zeta) : k),
      (-(3 / 4 * zeta) : k), (1 / 16 * eta : k), (-(1 / 2 * eta) : k),
      (-(1 / 4 * eta) : k), (2 * eta : k), (-(1 / 4 * theta) : k),
      (1 * theta : k)]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0],
      [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0],
      [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroPiQuarticNoG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuarticNoG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeG810 A B C D E F G) :
    (degreeZeroPiQuarticNoG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * G.natDegree := by
  rcases hcone with ⟨hGpos, hAlt, hBlt, hClt, hDlt, hElt, hFlt⟩
  have hA1 : 4 * A.natDegree + 1 ≤ G.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 8 * B.natDegree + 1 ≤ 3 * G.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : 2 * C.natDegree + 1 ≤ G.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 8 * D.natDegree + 1 ≤ 5 * G.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : 4 * E.natDegree + 1 ≤ 3 * G.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 8 * F.natDegree + 1 ≤ 7 * G.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPiQuarticNoG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_G_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeG810 A B C D E F G)
    (hdeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hGpos, hAlt, hBlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (5 / 4 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (piQuarticFaceG810 A B C D E F G).natDegree = 2 * G.natDegree := by
    simp only [piQuarticFaceG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroPiQuarticNoG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroPiQuartic810_eq_G_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hGpos, hAlt, hBlt, hClt, hDlt, hElt, hFlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoAB810` (34 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoAB810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoAB810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 16 : k), (63 / 262144 * l : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (7 / 8 * beta : k), (-(3 / 16 * gamma) : k),
      (3 / 4 * gamma : k), (5 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoAB810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoAB810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAB810 A B C D E F G) :
    (degreeZeroKappaQuarticNoAB810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroKappaQuarticNoAB810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_AB_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAB810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (5 / 512 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceAB810 A B C D E F G).natDegree = A.natDegree + 3 * B.natDegree := by
    simp only [kappaQuarticFaceAB810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoAB810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_AB_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hBpos, hAB, hClt, hDlt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoAC810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoAC810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoAC810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  exact speedRefl_degreeZeroMuQuarticNoC810_eq_polyOf l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoAC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAC810 A B C D E F G) :
    (degreeZeroMuQuarticNoAC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoAC810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_AC_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAC810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceAC810 A B C D E F G).natDegree = 3 * C.natDegree := by
    simp only [muQuarticFaceAC810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hCpos, hAC, hBlt, hDlt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoAD810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoAD810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoAD810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroMuQuarticNoAD810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoAD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAD810 A B C D E F G) :
    (degreeZeroMuQuarticNoAD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoAD810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_AD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAD810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceAD810 A B C D E F G).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [muQuarticFaceAD810]
    rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne), natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hDpos, hAD, hBlt, hClt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoAE810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoAE810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoAE810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(5 / 128) : k), (5 / 16 : k), (5 / 16 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  exact speedRefl_degreeZeroMuQuarticNoE810_eq_polyOf l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoAE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAE810 A B C D E F G) :
    (degreeZeroMuQuarticNoAE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * E.natDegree := by
  rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoAE810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_AE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAE810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceAE810 A B C D E F G).natDegree = 2 * E.natDegree := by
    simp only [muQuarticFaceAE810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoAE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_AE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hEpos, hAE, hBlt, hClt, hDlt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiQuarticNoAF810` (60 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoAF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoAF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (-(45 / 262144 * l) : k), (9 / 16384 * l : k), (-(9 / 16384 * l) : k),
      (-(9 / 8192 * l) : k), (9 / 4096 * l : k), (-(9 / 8192 * l) : k),
      (171 / 8192 * l : k), (9 / 1024 * l : k), (63 / 2048 * l : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 256 * l) : k), (-(27 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (7 / 2048 * beta : k), (-(7 / 1024 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 256 * beta : k), (7 / 512 * beta : k), (49 / 1024 * beta : k),
      (7 / 128 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 64 * gamma : k), (3 / 32 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (-(5 / 1024 * delta) : k),
      (5 / 128 * delta : k), (5 / 128 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 64 * delta) : k), (1 / 32 * epsilon : k),
      (-(3 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 16 * eta) : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0],
      [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  exact speedRefl_degreeZeroXiQuarticNoF810_eq_polyOf l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuarticNoAF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAF810 A B C D E F G) :
    (degreeZeroXiQuarticNoAF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * F.natDegree := by
  rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroXiQuarticNoAF810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_AF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAF810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (5 / 32 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (xiQuarticFaceAF810 A B C D E F G).natDegree = 2 * F.natDegree := by
    simp only [xiQuarticFaceAF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoAF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_AF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hFpos, hAF, hBlt, hClt, hDlt, hElt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPiQuarticNoAG810` (94 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoAG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoAG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (-(15 / 16) : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k), (45 / 131072 * l : k),
      (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k), (9 / 4096 * l : k),
      (9 / 4096 * l : k), (-(27 / 4096 * l) : k), (9 / 4096 * l : k),
      (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k), (-(27 / 1024 * l) : k),
      (9 / 512 * l : k), (63 / 1024 * l : k), (9 / 128 * l : k),
      (27 / 256 * l : k), (9 / 256 * l : k), (63 / 512 * l : k),
      (189 / 512 * l : k), (63 / 512 * l : k), (-(9 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(27 / 64 * l) : k), (-(9 / 32 * l) : k),
      (-(27 / 128 * l) : k), (-(9 / 16 * l) : k), (-(3 / 32 * l) : k),
      (9 / 8 * l : k), (7 / 4096 * beta : k), (7 / 4096 * beta : k),
      (-(7 / 1024 * beta) : k), (7 / 512 * beta : k), (7 / 512 * beta : k),
      (-(21 / 256 * beta) : k), (-(7 / 256 * beta) : k), (-(63 / 512 * beta) : k),
      (-(7 / 64 * beta) : k), (7 / 32 * beta : k), (21 / 128 * beta : k),
      (7 / 16 * beta : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (-(7 / 8 * beta) : k), (-(3 / 32 * gamma) : k), (-(15 / 256 * gamma) : k),
      (3 / 16 * gamma : k), (3 / 8 * gamma : k), (3 / 4 * gamma : k),
      (1 / 8 * gamma : k), (-(3 / 4 * gamma) : k), (-(3 / 4 * gamma) : k),
      (5 / 512 * delta : k), (-(15 / 256 * delta) : k), (-(5 / 128 * delta) : k),
      (5 / 32 * delta : k), (5 / 32 * delta : k), (15 / 32 * delta : k),
      (15 / 32 * delta : k), (-(5 / 8 * delta) : k), (-(5 / 4 * delta) : k),
      (1 / 4 * epsilon : k), (1 / 2 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k), (3 / 32 * zeta : k),
      (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 4 * zeta) : k),
      (-(3 / 4 * zeta) : k), (1 / 16 * eta : k), (-(1 / 2 * eta) : k),
      (-(1 / 4 * eta) : k), (2 * eta : k), (-(1 / 4 * theta) : k),
      (1 * theta : k)]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0],
      [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0],
      [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  exact speedRefl_degreeZeroPiQuarticNoG810_eq_polyOf l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuarticNoAG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAG810 A B C D E F G) :
    (degreeZeroPiQuarticNoAG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * G.natDegree := by
  rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPiQuarticNoAG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_AG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeAG810 A B C D E F G)
    (hdeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (5 / 4 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (piQuarticFaceAG810 A B C D E F G).natDegree = 2 * G.natDegree := by
    simp only [piQuarticFaceAG810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroPiQuarticNoAG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroPiQuartic810_eq_AG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, hGpos, hAG, hBlt, hClt, hDlt, hElt, hFlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoBC810` (34 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoBC810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoBC810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 16 : k), (63 / 262144 * l : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (7 / 8 * beta : k), (-(3 / 16 * gamma) : k),
      (3 / 4 * gamma : k), (5 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoBC810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoBC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBC810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + 2 * C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroKappaQuarticNoBC810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_BC_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBC810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaQuarticFaceBC810 A B C D E F G).natDegree = B.natDegree + 2 * C.natDegree := by
    simp only [kappaQuarticFaceBC810]
    rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoBC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BC_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hCpos, hBC, hAlt, hDlt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoBD810` (34 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoBD810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoBD810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 16 : k), (63 / 262144 * l : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (7 / 8 * beta : k), (-(3 / 16 * gamma) : k),
      (3 / 4 * gamma : k), (5 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoBD810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoBD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBD810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroKappaQuarticNoBD810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_BD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBD810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (kappaQuarticFaceBD810 A B C D E F G).natDegree = 2 * B.natDegree + D.natDegree := by
    simp only [kappaQuarticFaceBD810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
  have hrest := degreeZeroKappaQuarticNoBD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hDpos, hBD, hAlt, hClt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoBF810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoBF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoBF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (-(5 / 64) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  exact speedRefl_degreeZeroMuQuarticNoB810_eq_polyOf l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoBF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBF810 A B C D E F G) :
    (degreeZeroMuQuarticNoBF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoBF810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_BF_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBF810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
    omega
  have hc : (35 / 2048 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (muQuarticFaceBF810 A B C D E F G).natDegree = 4 * B.natDegree := by
    simp only [muQuarticFaceBF810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoBF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_BF_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hFpos, hBF, hAlt, hClt, hDlt, hElt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoBG810` (34 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoBG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoBG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (63 / 262144 * l : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (7 / 8 * beta : k), (-(3 / 16 * gamma) : k),
      (3 / 4 * gamma : k), (5 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoBG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoBG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBG810 A B C D E F G) :
    (degreeZeroKappaQuarticNoBG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      B.natDegree + G.natDegree := by
  rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hC1 : 3 * C.natDegree + 1 ≤ 4 * B.natDegree := Nat.succ_le_of_lt hClt
  have hD1 : 3 * D.natDegree + 1 ≤ 5 * B.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroKappaQuarticNoBG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_BG_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBG810 A B C D E F G)
    (hdeg : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
    omega
  have hc : (5 / 16 : k) ≠ 0 := div_ne_zero (by norm_num) (by norm_num)
  have hlead : (kappaQuarticFaceBG810 A B C D E F G).natDegree = B.natDegree + G.natDegree := by
    simp only [kappaQuarticFaceBG810]
    rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  have hrest := degreeZeroKappaQuarticNoBG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroKappaQuartic810_eq_BG_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, hGpos, hBG, hAlt, hClt, hDlt, hElt, hFlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroMuQuarticNoCD810` (42 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroMuQuarticNoCD810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuQuarticNoCD810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 4 * gamma : k), (-(5 / 1024 * delta) : k),
      (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k), (-(3 / 64 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]] := by
  exact speedRefl_degreeZeroMuQuarticNoC810_eq_polyOf l beta gamma delta epsilon zeta eta theta A B C D E F G


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuarticNoCD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCD810 A B C D E F G) :
    (degreeZeroMuQuarticNoCD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * C.natDegree := by
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hE1 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroMuQuarticNoCD810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_CD_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCD810 A B C D E F G)
    (hdeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
    omega
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (muQuarticFaceCD810 A B C D E F G).natDegree = 3 * C.natDegree := by
    simp only [muQuarticFaceCD810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := degreeZeroMuQuarticNoCD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroMuQuartic810_eq_CD_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hDpos, hCD, hAlt, hBlt, hElt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroXiQuarticNoCE810` (60 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroXiQuarticNoCE810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroXiQuarticNoCE810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k),
      (-(45 / 262144 * l) : k), (9 / 16384 * l : k), (-(9 / 16384 * l) : k),
      (-(9 / 8192 * l) : k), (9 / 4096 * l : k), (-(9 / 8192 * l) : k),
      (171 / 8192 * l : k), (9 / 1024 * l : k), (63 / 2048 * l : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 256 * l) : k), (-(27 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (-(7 / 8192 * beta) : k),
      (7 / 2048 * beta : k), (-(7 / 1024 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 256 * beta : k), (7 / 512 * beta : k), (49 / 1024 * beta : k),
      (7 / 128 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (3 / 64 * gamma : k), (3 / 32 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k), (-(5 / 1024 * delta) : k),
      (5 / 128 * delta : k), (5 / 128 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 64 * delta) : k), (1 / 32 * epsilon : k),
      (-(3 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k),
      (-(3 / 64 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 8 * zeta : k),
      (-(1 / 16 * eta) : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0],
      [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0],
      [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0]] := by
  simp only [degreeZeroXiQuarticNoCE810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiQuarticNoCE810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCE810 A B C D E F G) :
    (degreeZeroXiQuarticNoCE810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
  have hA1 : 2 * A.natDegree + 1 ≤ C.natDegree := Nat.succ_le_of_lt hAlt
  have hB1 : 4 * B.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 4 * D.natDegree + 1 ≤ 5 * C.natDegree := Nat.succ_le_of_lt hDlt
  have hF1 : 4 * F.natDegree + 1 ≤ 7 * C.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroXiQuarticNoCE810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega



set_option maxHeartbeats 64000000 in
theorem quarticCone_CE_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeCE810 A B C D E F G)
    (hdeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree =
        0) :
    False := by
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
    omega
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead : (xiQuarticFaceCE810 A B C D E F G).natDegree = 2 * C.natDegree + E.natDegree := by
    simp only [xiQuarticFaceCE810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
  have hrest := degreeZeroXiQuarticNoCE810_natDegree_lt l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone
  rw [degreeZeroXiQuartic810_eq_CE_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, hCE, hAlt, hBlt, hDlt, hFlt, hGlt⟩
  omega



set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroKappaQuarticNoCF810` (34 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroKappaQuarticNoCF810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuarticNoCF810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (63 / 262144 * l : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (7 / 8 * beta : k), (-(3 / 16 * gamma) : k),
      (3 / 4 * gamma : k), (5 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [degreeZeroKappaQuarticNoCF810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]


end QuarticKills810

end Max11DegreeRoutes

end
