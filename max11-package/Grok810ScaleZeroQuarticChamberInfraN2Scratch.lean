import Grok810ScaleZeroQuarticChamberN7LadderScratch
import Max11SpeedReflectDegLibScratch

/-! # `N₂` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroN2Quartic810` has 56 monomials.  `…ChamberFacesPart0Scratch` does this
for `κ, μ, ξ, π` only; `UNOWNED_CHAMBERS.md` needs the same for `ο`, `Π`
and the auxiliaries `N₂…N₇`.  Independent of the sibling
`…ChamberInfra*` modules.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

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

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberInfraN2810

/-! ## `N₂`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroN2Quartic810` (8 monomials). -/
def n2QuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN2Quartic810` (18 monomials). -/
def n2QuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * B * F)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

def n2QuarticColumnL810_live_InfraN2c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810_live_InfraN2c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnL810_live_InfraN2c1
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810_live_InfraN2c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * l : k), (315 / 262144 * l : k), (-(9 / 131072 * l) : k),
      (45 / 8192 * l : k), (-(9 / 8192 * l) : k), (27 / 16384 * l : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810_live_InfraN2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_live_InfraN2c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n2QuarticColumnL810_live_InfraN2c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnL810_live_InfraN2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n2QuarticColumnL810_live_InfraN2c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * B * F)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810_live_InfraN2c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnL810_live_InfraN2c2
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810_live_InfraN2c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 8192 * l : k), (315 / 32768 * l : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 512 * l : k), (-(9 / 1024 * l) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810_live_InfraN2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_live_InfraN2c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + G.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + 2 * D.natDegree < d) :
    (n2QuarticColumnL810_live_InfraN2c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnL810_live_InfraN2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n2QuarticColumnL810_live_InfraN2c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((63 / 1024 * l : k) • (B ^ 2 * E))
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810_live_InfraN2c3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnL810_live_InfraN2c3
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810_live_InfraN2c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810_live_InfraN2c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_live_InfraN2c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd12 : 2 * B.natDegree + E.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 3 * C.natDegree < d)
    (hd15 : C.natDegree + G.natDegree < d)
    (hd16 : D.natDegree + F.natDegree < d)
    (hd17 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810_live_InfraN2c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnL810_live_InfraN2c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + G.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + 2 * D.natDegree < d)
    (hd12 : 2 * B.natDegree + E.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 3 * C.natDegree < d)
    (hd15 : C.natDegree + G.natDegree < d)
    (hd16 : D.natDegree + F.natDegree < d)
    (hd17 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
  have hsplit : n2QuarticColumnL810 l A B C D E F G = n2QuarticColumnL810_live_InfraN2c1 l A B C D E F G + n2QuarticColumnL810_live_InfraN2c2 l A B C D E F G + n2QuarticColumnL810_live_InfraN2c3 l A B C D E F G := by
    simp only [n2QuarticColumnL810, n2QuarticColumnL810_live_InfraN2c1, n2QuarticColumnL810_live_InfraN2c2, n2QuarticColumnL810_live_InfraN2c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n2QuarticColumnL810_live_InfraN2c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnL810_live_InfraN2c2_natDegree_lt l A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (n2QuarticColumnL810_live_InfraN2c3_natDegree_lt l A B C D E F G hd12 hd13 hd14 hd15 hd16 hd17)))


theorem n2QuarticColumnL810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnL810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnL810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN2Quartic810` (11 monomials). -/
def n2QuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

def n2QuarticColumnBeta810_live_InfraN2c1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810_live_InfraN2c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnBeta810_live_InfraN2c1
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810_live_InfraN2c1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * beta : k), (35 / 8192 * beta : k), (7 / 16384 * beta : k),
      (21 / 1024 * beta : k), (7 / 512 * beta : k), (-(7 / 1024 * beta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810_live_InfraN2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_live_InfraN2c1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n2QuarticColumnBeta810_live_InfraN2c1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnBeta810_live_InfraN2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n2QuarticColumnBeta810_live_InfraN2c2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810_live_InfraN2c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnBeta810_live_InfraN2c2
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810_live_InfraN2c2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810_live_InfraN2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_live_InfraN2c2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd6 : 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + G.natDegree < d)
    (hd8 : B.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + E.natDegree < d)
    (hd10 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810_live_InfraN2c2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnBeta810_live_InfraN2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + G.natDegree < d)
    (hd8 : B.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + E.natDegree < d)
    (hd10 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  have hsplit : n2QuarticColumnBeta810 beta A B C D E F G = n2QuarticColumnBeta810_live_InfraN2c1 beta A B C D E F G + n2QuarticColumnBeta810_live_InfraN2c2 beta A B C D E F G := by
    simp only [n2QuarticColumnBeta810, n2QuarticColumnBeta810_live_InfraN2c1, n2QuarticColumnBeta810_live_InfraN2c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n2QuarticColumnBeta810_live_InfraN2c1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnBeta810_live_InfraN2c2_natDegree_lt beta A B C D E F G hd6 hd7 hd8 hd9 hd10)))


theorem n2QuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroN2Quartic810` (3 monomials). -/
def n2QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnGamma810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 128 * gamma : k), (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k)
      ]
      [
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * B.natDegree < d)
    (hd1 : B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + D.natDegree < d) :
    (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n2QuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroN2Quartic810` (7 monomials). -/
def n2QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • A ^ 4
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G

def n2QuarticColumnDelta810_live_InfraN2c1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • A ^ 4
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnDelta810_live_InfraN2c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnDelta810_live_InfraN2c1
    (delta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810_live_InfraN2c1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * delta : k), (15 / 1024 * delta : k), (15 / 1024 * delta : k),
      (5 / 64 * delta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n2QuarticColumnDelta810_live_InfraN2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810_live_InfraN2c1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d) :
    (n2QuarticColumnDelta810_live_InfraN2c1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnDelta810_live_InfraN2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n2QuarticColumnDelta810_live_InfraN2c2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 * delta : k) • (B * D))
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnDelta810_live_InfraN2c2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnDelta810_live_InfraN2c2
    (delta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810_live_InfraN2c2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n2QuarticColumnDelta810_live_InfraN2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810_live_InfraN2c2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n2QuarticColumnDelta810_live_InfraN2c2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnDelta810_live_InfraN2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : n2QuarticColumnDelta810 delta A B C D E F G = n2QuarticColumnDelta810_live_InfraN2c1 delta A B C D E F G + n2QuarticColumnDelta810_live_InfraN2c2 delta A B C D E F G := by
    simp only [n2QuarticColumnDelta810, n2QuarticColumnDelta810_live_InfraN2c1, n2QuarticColumnDelta810_live_InfraN2c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n2QuarticColumnDelta810_live_InfraN2c1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3) (n2QuarticColumnDelta810_live_InfraN2c2_natDegree_lt delta A B C D E F G hd4 hd5 hd6)))


theorem n2QuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroN2Quartic810` (2 monomials). -/
def n2QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 4 * epsilon : k)) • (B * C)
  + (1 / 2 * epsilon : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnEpsilon810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k)
      ]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [n2QuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n2QuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroN2Quartic810` (4 monomials). -/
def n2QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * zeta : k) • A ^ 3
  + (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnZeta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 1024 * zeta : k), (3 / 64 * zeta : k), (-(15 / 128 * zeta) : k),
      (3 / 8 * zeta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n2QuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n2QuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroN2Quartic810` (1 monomials). -/
def n2QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • D

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnEta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)
      ]
      [
      [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : D.natDegree < d) :
    (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n2QuarticColumnEta810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroN2Quartic810` (2 monomials). -/
def n2QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnTheta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN2_n2QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * theta : k), (1 / 8 * theta : k)
      ]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN2_n2QuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n2QuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    n2QuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [n2QuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroN2Quartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroN2Quartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticLoadFree810 A B C D E F G +
      n2QuarticColumnL810 l A B C D E F G +
      n2QuarticColumnBeta810 beta A B C D E F G +
      n2QuarticColumnGamma810 gamma A B C D E F G +
      n2QuarticColumnDelta810 delta A B C D E F G +
      n2QuarticColumnEpsilon810 epsilon A B C D E F G +
      n2QuarticColumnZeta810 zeta A B C D E F G +
      n2QuarticColumnEta810 eta A B C D E F G +
      n2QuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, n2QuarticLoadFree810, n2QuarticColumnL810, n2QuarticColumnBeta810, n2QuarticColumnGamma810, n2QuarticColumnDelta810, n2QuarticColumnEpsilon810, n2QuarticColumnZeta810, n2QuarticColumnEta810, n2QuarticColumnTheta810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraN2810

end Max11DegreeRoutes
