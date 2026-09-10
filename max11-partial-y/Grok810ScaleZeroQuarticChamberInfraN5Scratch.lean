import Grok810ScaleZeroQuarticChamberN7LadderScratch
import Max11SpeedReflectDegLibScratch

/-! # `N₅` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroN5Quartic810` has 89 monomials.  `…ChamberFacesPart0Scratch` does this
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

section QuarticChamberInfraN5810

/-! ## `N₅`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroN5Quartic810` (14 monomials). -/
def n5QuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN5Quartic810`, chunk 1/2 (20 monomials). -/
def n5QuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  - (225 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (315 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 65536 * l : k) • (A ^ 3 * B * D)
  + (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  + (9 / 65536 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (441 / 262144 * l : k) • (A * B ^ 4)
  + (45 / 8192 * l : k) • (A ^ 3 * G)
  - (27 / 8192 * l : k) • (A ^ 2 * B * F)
  + (27 / 4096 * l : k) • (A ^ 2 * C * E)
  - (9 / 16384 * l : k) • (A ^ 2 * D ^ 2)
  + (27 / 8192 * l : k) • (A * B ^ 2 * E)
  + (9 / 1024 * l : k) • (A * B * C * D)
  - (3 / 2048 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 256 * l : k) • (A * C * G)
  - (9 / 512 * l : k) • (A * D * F)
  + (9 / 1024 * l : k) • (A * E ^ 2)

def n5QuarticColumnL1810_live_InfraN5c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  - (225 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (315 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 65536 * l : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810_live_InfraN5c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c1
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810_live_InfraN5c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (429 / 33554432 * l : k), (315 / 1048576 * l : k), (-(225 / 4194304 * l) : k),
      (315 / 262144 * l : k), (-(27 / 65536 * l) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810_live_InfraN5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_live_InfraN5c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n5QuarticColumnL1810_live_InfraN5c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnL1810_live_InfraN5c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  + (9 / 65536 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (441 / 262144 * l : k) • (A * B ^ 4)
  + (45 / 8192 * l : k) • (A ^ 3 * G)
  - (27 / 8192 * l : k) • (A ^ 2 * B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810_live_InfraN5c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c2
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810_live_InfraN5c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (135 / 131072 * l : k), (9 / 65536 * l : k), (-(441 / 262144 * l) : k),
      (45 / 8192 * l : k), (-(27 / 8192 * l) : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticColumnL1810_live_InfraN5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_live_InfraN5c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 3 * A.natDegree + G.natDegree < d)
    (hd9 : 2 * A.natDegree + B.natDegree + F.natDegree < d) :
    (n5QuarticColumnL1810_live_InfraN5c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnL1810_live_InfraN5c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 4096 * l : k) • (A ^ 2 * C * E)
  - (9 / 16384 * l : k) • (A ^ 2 * D ^ 2)
  + (27 / 8192 * l : k) • (A * B ^ 2 * E)
  + (9 / 1024 * l : k) • (A * B * C * D)
  - (3 / 2048 * l : k) • (A * C ^ 3)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810_live_InfraN5c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c3
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810_live_InfraN5c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 4096 * l : k), (-(9 / 16384 * l) : k), (27 / 8192 * l : k),
      (9 / 1024 * l : k), (-(3 / 2048 * l) : k)
      ]
      [
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0],
      [1, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810_live_InfraN5c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_live_InfraN5c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : A.natDegree + 3 * C.natDegree < d) :
    (n5QuarticColumnL1810_live_InfraN5c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnL1810_live_InfraN5c4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 256 * l : k) • (A * C * G)
  - (9 / 512 * l : k) • (A * D * F)
  + (9 / 1024 * l : k) • (A * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810_live_InfraN5c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c4
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810_live_InfraN5c4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (189 / 8192 * l : k), (567 / 16384 * l : k), (9 / 256 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k)
      ]
      [
      [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0],
      [1, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810_live_InfraN5c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_live_InfraN5c4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : 3 * B.natDegree + D.natDegree < d)
    (hd16 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd18 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd19 : A.natDegree + 2 * E.natDegree < d) :
    (n5QuarticColumnL1810_live_InfraN5c4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnL1810_live_InfraN5c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 3 * A.natDegree + G.natDegree < d)
    (hd9 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : A.natDegree + 3 * C.natDegree < d)
    (hd15 : 3 * B.natDegree + D.natDegree < d)
    (hd16 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd18 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd19 : A.natDegree + 2 * E.natDegree < d) :
    (n5QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  have hsplit : n5QuarticColumnL1810 l A B C D E F G = n5QuarticColumnL1810_live_InfraN5c1 l A B C D E F G + n5QuarticColumnL1810_live_InfraN5c2 l A B C D E F G + n5QuarticColumnL1810_live_InfraN5c3 l A B C D E F G + n5QuarticColumnL1810_live_InfraN5c4 l A B C D E F G := by
    simp only [n5QuarticColumnL1810, n5QuarticColumnL1810_live_InfraN5c1, n5QuarticColumnL1810_live_InfraN5c2, n5QuarticColumnL1810_live_InfraN5c3, n5QuarticColumnL1810_live_InfraN5c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n5QuarticColumnL1810_live_InfraN5c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (n5QuarticColumnL1810_live_InfraN5c2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n5QuarticColumnL1810_live_InfraN5c3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n5QuarticColumnL1810_live_InfraN5c4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem n5QuarticColumnL1810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN5Quartic810`, chunk 2/2 (7 monomials). -/
def n5QuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 1024 * l : k)) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2

def n5QuarticColumnL2810_live_InfraN5c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 1024 * l : k)) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL2810_live_InfraN5c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnL2810_live_InfraN5c1
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL2810_live_InfraN5c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnL2810_live_InfraN5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_live_InfraN5c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * B.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree + E.natDegree < d) :
    (n5QuarticColumnL2810_live_InfraN5c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnL2810_live_InfraN5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnL2810_live_InfraN5c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((27 / 512 * l : k) • (C * D ^ 2))
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL2810_live_InfraN5c2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnL2810_live_InfraN5c2
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL2810_live_InfraN5c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 512 * l) : k), (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n5QuarticColumnL2810_live_InfraN5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_live_InfraN5c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd4 : C.natDegree + 2 * D.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (n5QuarticColumnL2810_live_InfraN5c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnL2810_live_InfraN5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * B.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (n5QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  have hsplit : n5QuarticColumnL2810 l A B C D E F G = n5QuarticColumnL2810_live_InfraN5c1 l A B C D E F G + n5QuarticColumnL2810_live_InfraN5c2 l A B C D E F G := by
    simp only [n5QuarticColumnL2810, n5QuarticColumnL2810_live_InfraN5c1, n5QuarticColumnL2810_live_InfraN5c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n5QuarticColumnL2810_live_InfraN5c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3) (n5QuarticColumnL2810_live_InfraN5c2_natDegree_lt l A B C D E F G hd4 hd5 hd6)))


theorem n5QuarticColumnL2810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN5Quartic810` (16 monomials). -/
def n5QuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)
  - (7 / 2048 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

def n5QuarticColumnBeta810_live_InfraN5c1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810_live_InfraN5c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnBeta810_live_InfraN5c1
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810_live_InfraN5c1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * beta : k), (35 / 32768 * beta : k), (-(21 / 131072 * beta) : k),
      (35 / 8192 * beta : k), (-(7 / 8192 * beta) : k), (21 / 16384 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810_live_InfraN5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_live_InfraN5c1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n5QuarticColumnBeta810_live_InfraN5c1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnBeta810_live_InfraN5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnBeta810_live_InfraN5c2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((7 / 2048 * beta : k) • (A * B ^ 2 * C))
  - (189 / 32768 * beta : k) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810_live_InfraN5c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnBeta810_live_InfraN5c2
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810_live_InfraN5c2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 2048 * beta) : k), (-(189 / 32768 * beta) : k), (21 / 1024 * beta : k),
      (-(7 / 512 * beta) : k), (7 / 1024 * beta : k), (35 / 1024 * beta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810_live_InfraN5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_live_InfraN5c2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + G.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d) :
    (n5QuarticColumnBeta810_live_InfraN5c2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnBeta810_live_InfraN5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnBeta810_live_InfraN5c3
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810_live_InfraN5c3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnBeta810_live_InfraN5c3
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810_live_InfraN5c3 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810_live_InfraN5c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_live_InfraN5c3_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n5QuarticColumnBeta810_live_InfraN5c3 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnBeta810_live_InfraN5c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
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
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n5QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  have hsplit : n5QuarticColumnBeta810 beta A B C D E F G = n5QuarticColumnBeta810_live_InfraN5c1 beta A B C D E F G + n5QuarticColumnBeta810_live_InfraN5c2 beta A B C D E F G + n5QuarticColumnBeta810_live_InfraN5c3 beta A B C D E F G := by
    simp only [n5QuarticColumnBeta810, n5QuarticColumnBeta810_live_InfraN5c1, n5QuarticColumnBeta810_live_InfraN5c2, n5QuarticColumnBeta810_live_InfraN5c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n5QuarticColumnBeta810_live_InfraN5c1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnBeta810_live_InfraN5c2_natDegree_lt beta A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (n5QuarticColumnBeta810_live_InfraN5c3_natDegree_lt beta A B C D E F G hd12 hd13 hd14 hd15)))


theorem n5QuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroN5Quartic810` (5 monomials). -/
def n5QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 256 * gamma : k)) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnGamma810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 256 * gamma) : k), (9 / 128 * gamma : k), (9 / 128 * gamma : k),
      (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (n5QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n5QuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroN5Quartic810` (11 monomials). -/
def n5QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

def n5QuarticColumnDelta810_live_InfraN5c1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810_live_InfraN5c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnDelta810_live_InfraN5c1
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810_live_InfraN5c1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * delta : k), (15 / 4096 * delta : k), (-(5 / 16384 * delta) : k),
      (15 / 1024 * delta : k), (5 / 512 * delta : k), (-(5 / 1024 * delta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810_live_InfraN5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_live_InfraN5c1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n5QuarticColumnDelta810_live_InfraN5c1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnDelta810_live_InfraN5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnDelta810_live_InfraN5c2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810_live_InfraN5c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnDelta810_live_InfraN5c2
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810_live_InfraN5c2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 * delta : k), (5 / 64 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810_live_InfraN5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_live_InfraN5c2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd6 : 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + G.natDegree < d)
    (hd8 : B.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + E.natDegree < d)
    (hd10 : 2 * D.natDegree < d) :
    (n5QuarticColumnDelta810_live_InfraN5c2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnDelta810_live_InfraN5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
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
    (n5QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : n5QuarticColumnDelta810 delta A B C D E F G = n5QuarticColumnDelta810_live_InfraN5c1 delta A B C D E F G + n5QuarticColumnDelta810_live_InfraN5c2 delta A B C D E F G := by
    simp only [n5QuarticColumnDelta810, n5QuarticColumnDelta810_live_InfraN5c1, n5QuarticColumnDelta810_live_InfraN5c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n5QuarticColumnDelta810_live_InfraN5c1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnDelta810_live_InfraN5c2_natDegree_lt delta A B C D E F G hd6 hd7 hd8 hd9 hd10)))


theorem n5QuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroN5Quartic810` (3 monomials). -/
def n5QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnEpsilon810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 32 * epsilon : k), (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k)
      ]
      [
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * B.natDegree < d)
    (hd1 : B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + D.natDegree < d) :
    (n5QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n5QuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroN5Quartic810` (7 monomials). -/
def n5QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G

def n5QuarticColumnZeta810_live_InfraN5c1
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnZeta810_live_InfraN5c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnZeta810_live_InfraN5c1
    (zeta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810_live_InfraN5c1 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * zeta : k), (3 / 256 * zeta : k), (3 / 1024 * zeta : k),
      (3 / 64 * zeta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnZeta810_live_InfraN5c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_live_InfraN5c1_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d) :
    (n5QuarticColumnZeta810_live_InfraN5c1 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnZeta810_live_InfraN5c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n5QuarticColumnZeta810_live_InfraN5c2
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 64 * zeta : k) • (B * D))
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnZeta810_live_InfraN5c2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnZeta810_live_InfraN5c2
    (zeta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810_live_InfraN5c2 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n5QuarticColumnZeta810_live_InfraN5c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_live_InfraN5c2_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n5QuarticColumnZeta810_live_InfraN5c2 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnZeta810_live_InfraN5c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n5QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  have hsplit : n5QuarticColumnZeta810 zeta A B C D E F G = n5QuarticColumnZeta810_live_InfraN5c1 zeta A B C D E F G + n5QuarticColumnZeta810_live_InfraN5c2 zeta A B C D E F G := by
    simp only [n5QuarticColumnZeta810, n5QuarticColumnZeta810_live_InfraN5c1, n5QuarticColumnZeta810_live_InfraN5c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n5QuarticColumnZeta810_live_InfraN5c1_natDegree_lt zeta A B C D E F G hd0 hd1 hd2 hd3) (n5QuarticColumnZeta810_live_InfraN5c2_natDegree_lt zeta A B C D E F G hd4 hd5 hd6)))


theorem n5QuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroN5Quartic810` (2 monomials). -/
def n5QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 32 * eta : k)) • (B * C)
  + (1 / 4 * eta : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnEta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 32 * eta) : k), (1 / 4 * eta : k)
      ]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (n5QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n5QuarticColumnEta810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroN5Quartic810` (4 monomials). -/
def n5QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnTheta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN5_n5QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 1024 * theta : k), (1 / 32 * theta : k), (-(3 / 128 * theta) : k),
      (1 / 8 * theta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (n5QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN5_n5QuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n5QuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    n5QuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [n5QuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroN5Quartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroN5Quartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticLoadFree810 A B C D E F G +
      n5QuarticColumnL1810 l A B C D E F G +
      n5QuarticColumnL2810 l A B C D E F G +
      n5QuarticColumnBeta810 beta A B C D E F G +
      n5QuarticColumnGamma810 gamma A B C D E F G +
      n5QuarticColumnDelta810 delta A B C D E F G +
      n5QuarticColumnEpsilon810 epsilon A B C D E F G +
      n5QuarticColumnZeta810 zeta A B C D E F G +
      n5QuarticColumnEta810 eta A B C D E F G +
      n5QuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroN5Quartic810, n5QuarticLoadFree810, n5QuarticColumnL1810, n5QuarticColumnL2810, n5QuarticColumnBeta810, n5QuarticColumnGamma810, n5QuarticColumnDelta810, n5QuarticColumnEpsilon810, n5QuarticColumnZeta810, n5QuarticColumnEta810, n5QuarticColumnTheta810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraN5810

end Max11DegreeRoutes
