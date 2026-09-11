import Grok810ScaleZeroQuarticChamberAuxTowerScratch

/-! # `N₇` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroN7Quartic810` has 136 monomials.  `…ChamberFacesPart0Scratch` does this
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

section QuarticChamberInfraN7810

/-! ## `N₇`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroN7Quartic810` (21 monomials). -/
def n7QuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * B ^ 3 * C)
  + (23 / 8192 : k) • (A * B ^ 5)
  - (5 / 512 : k) • (A * B ^ 3 * E)
  + (15 / 512 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 64 : k) • (A * B * C * G)
  - (5 / 64 : k) • (A * C ^ 2 * F)
  - (5 / 64 : k) • (A * C * D * E)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN7Quartic810`, chunk 1/2 (20 monomials). -/
def n7QuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (6435 / 268435456 * l : k) • A ^ 8
  + (315 / 524288 * l : k) • (A ^ 6 * C)
  - (315 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (315 / 131072 * l : k) • (A ^ 5 * E)
  - (315 / 262144 * l : k) • (A ^ 4 * B * D)
  + (1485 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (63 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  - (45 / 524288 * l : k) • (A ^ 2 * B ^ 4)
  + (315 / 32768 * l : k) • (A ^ 4 * G)
  - (45 / 8192 * l : k) • (A ^ 3 * B * F)
  + (171 / 8192 * l : k) • (A ^ 3 * C * E)
  - (45 / 16384 * l : k) • (A ^ 3 * D ^ 2)
  - (45 / 16384 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C * D)
  - (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  - (27 / 4096 * l : k) • (A * B ^ 3 * D)
  + (45 / 4096 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 128 * l : k) • (A ^ 2 * C * G)
  - (27 / 1024 * l : k) • (A ^ 2 * D * F)

def n7QuarticColumnL1810_live_InfraN7c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (6435 / 268435456 * l : k) • A ^ 8
  + (315 / 524288 * l : k) • (A ^ 6 * C)
  - (315 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (315 / 131072 * l : k) • (A ^ 5 * E)
  - (315 / 262144 * l : k) • (A ^ 4 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL1810_live_InfraN7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c1
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL1810_live_InfraN7c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (6435 / 268435456 * l : k), (315 / 524288 * l : k), (-(315 / 2097152 * l) : k),
      (315 / 131072 * l : k), (-(315 / 262144 * l) : k)
      ]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnL1810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n7QuarticColumnL1810_live_InfraN7c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnL1810_live_InfraN7c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1485 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (63 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  - (45 / 524288 * l : k) • (A ^ 2 * B ^ 4)
  + (315 / 32768 * l : k) • (A ^ 4 * G)
  - (45 / 8192 * l : k) • (A ^ 3 * B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL1810_live_InfraN7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c2
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL1810_live_InfraN7c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1485 / 524288 * l : k), (-(63 / 131072 * l) : k), (-(45 / 524288 * l) : k),
      (315 / 32768 * l : k), (-(45 / 8192 * l) : k)
      ]
      [
      [4, 0, 2, 0, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1],
      [3, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticColumnL1810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd8 : 4 * A.natDegree + G.natDegree < d)
    (hd9 : 3 * A.natDegree + B.natDegree + F.natDegree < d) :
    (n7QuarticColumnL1810_live_InfraN7c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnL1810_live_InfraN7c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (171 / 8192 * l : k) • (A ^ 3 * C * E)
  - (45 / 16384 * l : k) • (A ^ 3 * D ^ 2)
  - (45 / 16384 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C * D)
  - (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL1810_live_InfraN7c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c3
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL1810_live_InfraN7c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (171 / 8192 * l : k), (-(45 / 16384 * l) : k), (-(45 / 16384 * l) : k),
      (9 / 4096 * l : k), (-(9 / 8192 * l) : k)
      ]
      [
      [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnL1810_live_InfraN7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_live_InfraN7c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 3 * C.natDegree < d) :
    (n7QuarticColumnL1810_live_InfraN7c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnL1810_live_InfraN7c4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((27 / 4096 * l : k) • (A * B ^ 3 * D))
  + (45 / 4096 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 128 * l : k) • (A ^ 2 * C * G)
  - (27 / 1024 * l : k) • (A ^ 2 * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL1810_live_InfraN7c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c4
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL1810_live_InfraN7c4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 4096 * l) : k), (45 / 4096 * l : k), (-(567 / 16384 * l) : k),
      (9 / 128 * l : k), (-(27 / 1024 * l) : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1],
      [2, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [n7QuarticColumnL1810_live_InfraN7c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_live_InfraN7c4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd16 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : 4 * B.natDegree + C.natDegree < d)
    (hd18 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd19 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (n7QuarticColumnL1810_live_InfraN7c4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL1810_live_InfraN7c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd8 : 4 * A.natDegree + G.natDegree < d)
    (hd9 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd15 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd16 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : 4 * B.natDegree + C.natDegree < d)
    (hd18 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd19 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (n7QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnL1810 l A B C D E F G = n7QuarticColumnL1810_live_InfraN7c1 l A B C D E F G + n7QuarticColumnL1810_live_InfraN7c2 l A B C D E F G + n7QuarticColumnL1810_live_InfraN7c3 l A B C D E F G + n7QuarticColumnL1810_live_InfraN7c4 l A B C D E F G := by
    simp only [n7QuarticColumnL1810, n7QuarticColumnL1810_live_InfraN7c1, n7QuarticColumnL1810_live_InfraN7c2, n7QuarticColumnL1810_live_InfraN7c3, n7QuarticColumnL1810_live_InfraN7c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnL1810_live_InfraN7c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticColumnL1810_live_InfraN7c2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n7QuarticColumnL1810_live_InfraN7c3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n7QuarticColumnL1810_live_InfraN7c4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem n7QuarticColumnL1810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN7Quartic810`, chunk 2/2 (19 monomials). -/
def n7QuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (81 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  - (9 / 512 * l : k) • (A * B ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * C * F)
  - (9 / 256 * l : k) • (A * C ^ 2 * E)
  - (9 / 512 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 32 * l : k) • (A * E * G)
  - (9 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

def n7QuarticColumnL2810_live_InfraN7c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (81 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  - (9 / 512 * l : k) • (A * B ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * C * F)
  - (9 / 256 * l : k) • (A * C ^ 2 * E)
  - (9 / 512 * l : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL2810_live_InfraN7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c1
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL2810_live_InfraN7c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (81 / 2048 * l : k), (-(9 / 512 * l) : k), (-(9 / 256 * l) : k),
      (-(9 / 256 * l) : k), (-(9 / 512 * l) : k)
      ]
      [
      [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnL2810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (n7QuarticColumnL2810_live_InfraN7c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnL2810_live_InfraN7c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL2810_live_InfraN7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c2
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL2810_live_InfraN7c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 512 * l : k), (45 / 256 * l : k), (45 / 512 * l : k),
      (189 / 1024 * l : k), (63 / 4096 * l : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnL2810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d) :
    (n7QuarticColumnL2810_live_InfraN7c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnL2810_live_InfraN7c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 32 * l : k) • (A * E * G)
  - (9 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL2810_live_InfraN7c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c3
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL2810_live_InfraN7c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 32 * l : k), (-(9 / 128 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(9 / 128 * l) : k)
      ]
      [
      [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 2, 0, 0, 0, 1]
      ] := by
  simp only [n7QuarticColumnL2810_live_InfraN7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_live_InfraN7c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d) :
    (n7QuarticColumnL2810_live_InfraN7c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnL2810_live_InfraN7c4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 32 * l : k) • (C * D * F))
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnL2810_live_InfraN7c4` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c4
    (l : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnL2810_live_InfraN7c4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 32 * l) : k), (-(9 / 64 * l) : k), (-(9 / 64 * l) : k),
      (9 / 16 * l : k)
      ]
      [
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [n7QuarticColumnL2810_live_InfraN7c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_live_InfraN7c4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d) :
    (n7QuarticColumnL2810_live_InfraN7c4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnL2810_live_InfraN7c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d)
    (hd10 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d) :
    (n7QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnL2810 l A B C D E F G = n7QuarticColumnL2810_live_InfraN7c1 l A B C D E F G + n7QuarticColumnL2810_live_InfraN7c2 l A B C D E F G + n7QuarticColumnL2810_live_InfraN7c3 l A B C D E F G + n7QuarticColumnL2810_live_InfraN7c4 l A B C D E F G := by
    simp only [n7QuarticColumnL2810, n7QuarticColumnL2810_live_InfraN7c1, n7QuarticColumnL2810_live_InfraN7c2, n7QuarticColumnL2810_live_InfraN7c3, n7QuarticColumnL2810_live_InfraN7c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnL2810_live_InfraN7c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticColumnL2810_live_InfraN7c2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n7QuarticColumnL2810_live_InfraN7c3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n7QuarticColumnL2810_live_InfraN7c4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18)))


theorem n7QuarticColumnL2810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN7Quartic810`, chunk 1/2 (20 monomials). -/
def n7QuarticColumnBeta1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 4194304 * beta : k) • A ^ 7
  + (35 / 16384 * beta : k) • (A ^ 5 * C)
  - (35 / 65536 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 4 * E)
  - (35 / 8192 * beta : k) • (A ^ 3 * B * D)
  + (91 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  - (35 / 16384 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (49 / 32768 * beta : k) • (A * B ^ 4)
  + (35 / 1024 * beta : k) • (A ^ 3 * G)
  - (21 / 1024 * beta : k) • (A ^ 2 * B * F)
  + (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  - (21 / 2048 * beta : k) • (A ^ 2 * D ^ 2)
  - (7 / 1024 * beta : k) • (A * B ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * C * D)
  + (7 / 512 * beta : k) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  - (7 / 64 * beta : k) • (A * D * F)
  + (7 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)

def n7QuarticColumnBeta1810_live_InfraN7c1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 4194304 * beta : k) • A ^ 7
  + (35 / 16384 * beta : k) • (A ^ 5 * C)
  - (35 / 65536 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 4 * E)
  - (35 / 8192 * beta : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnBeta1810_live_InfraN7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c1
    (beta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnBeta1810_live_InfraN7c1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (429 / 4194304 * beta : k), (35 / 16384 * beta : k), (-(35 / 65536 * beta) : k),
      (35 / 4096 * beta : k), (-(35 / 8192 * beta) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnBeta1810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n7QuarticColumnBeta1810_live_InfraN7c1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnBeta1810_live_InfraN7c2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (91 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  - (35 / 16384 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (49 / 32768 * beta : k) • (A * B ^ 4)
  + (35 / 1024 * beta : k) • (A ^ 3 * G)
  - (21 / 1024 * beta : k) • (A ^ 2 * B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnBeta1810_live_InfraN7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c2
    (beta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnBeta1810_live_InfraN7c2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (91 / 16384 * beta : k), (-(35 / 16384 * beta) : k), (49 / 32768 * beta : k),
      (35 / 1024 * beta : k), (-(21 / 1024 * beta) : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticColumnBeta1810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 3 * A.natDegree + G.natDegree < d)
    (hd9 : 2 * A.natDegree + B.natDegree + F.natDegree < d) :
    (n7QuarticColumnBeta1810_live_InfraN7c2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnBeta1810_live_InfraN7c3
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  - (21 / 2048 * beta : k) • (A ^ 2 * D ^ 2)
  - (7 / 1024 * beta : k) • (A * B ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * C * D)
  + (7 / 512 * beta : k) • (A * C ^ 3)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnBeta1810_live_InfraN7c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c3
    (beta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnBeta1810_live_InfraN7c3 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 1024 * beta : k), (-(21 / 2048 * beta) : k), (-(7 / 1024 * beta) : k),
      (7 / 256 * beta : k), (7 / 512 * beta : k)
      ]
      [
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0],
      [1, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnBeta1810_live_InfraN7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_live_InfraN7c3_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : A.natDegree + 3 * C.natDegree < d) :
    (n7QuarticColumnBeta1810_live_InfraN7c3 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnBeta1810_live_InfraN7c4
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((7 / 128 * beta : k) • (B ^ 3 * D))
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  - (7 / 64 * beta : k) • (A * D * F)
  + (7 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnBeta1810_live_InfraN7c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c4
    (beta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnBeta1810_live_InfraN7c4 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k), (-(7 / 64 * beta) : k),
      (7 / 128 * beta : k), (7 / 32 * beta : k)
      ]
      [
      [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 2, 0, 0],
      [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticColumnBeta1810_live_InfraN7c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_live_InfraN7c4_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd15 : 3 * B.natDegree + D.natDegree < d)
    (hd16 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd18 : A.natDegree + 2 * E.natDegree < d)
    (hd19 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n7QuarticColumnBeta1810_live_InfraN7c4 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta1810_live_InfraN7c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_natDegree_lt
    {d : ℕ}
    (beta : k)
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
    (hd17 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd18 : A.natDegree + 2 * E.natDegree < d)
    (hd19 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n7QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnBeta1810 beta A B C D E F G = n7QuarticColumnBeta1810_live_InfraN7c1 beta A B C D E F G + n7QuarticColumnBeta1810_live_InfraN7c2 beta A B C D E F G + n7QuarticColumnBeta1810_live_InfraN7c3 beta A B C D E F G + n7QuarticColumnBeta1810_live_InfraN7c4 beta A B C D E F G := by
    simp only [n7QuarticColumnBeta1810, n7QuarticColumnBeta1810_live_InfraN7c1, n7QuarticColumnBeta1810_live_InfraN7c2, n7QuarticColumnBeta1810_live_InfraN7c3, n7QuarticColumnBeta1810_live_InfraN7c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnBeta1810_live_InfraN7c1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticColumnBeta1810_live_InfraN7c2_natDegree_lt beta A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n7QuarticColumnBeta1810_live_InfraN7c3_natDegree_lt beta A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n7QuarticColumnBeta1810_live_InfraN7c4_natDegree_lt beta A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem n7QuarticColumnBeta1810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnBeta1810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnBeta1810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN7Quartic810`, chunk 2/2 (4 monomials). -/
def n7QuarticColumnBeta2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnBeta2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnBeta2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 32 * beta : k), (7 / 64 * beta : k), (7 / 64 * beta : k),
      (-(7 / 16 * beta) : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n7QuarticColumnBeta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (n7QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnBeta2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n7QuarticColumnBeta2810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnBeta2810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnBeta2810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroN7Quartic810` (8 monomials). -/
def n7QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 16 * gamma : k) • (A * C * F)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

def n7QuarticColumnGamma810_live_InfraN7c1
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 16 * gamma : k) • (A * C * F)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnGamma810_live_InfraN7c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnGamma810_live_InfraN7c1
    (gamma : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnGamma810_live_InfraN7c1 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * gamma : k), (-(27 / 256 * gamma) : k), (-(3 / 16 * gamma) : k),
      (9 / 64 * gamma : k)
      ]
      [
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [0, 2, 0, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticColumnGamma810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnGamma810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d) :
    (n7QuarticColumnGamma810_live_InfraN7c1 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnGamma810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnGamma810_live_InfraN7c2
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnGamma810_live_InfraN7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnGamma810_live_InfraN7c2
    (gamma : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnGamma810_live_InfraN7c2 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * gamma : k), (3 / 16 * gamma : k), (3 / 16 * gamma : k),
      (-(3 / 4 * gamma) : k)
      ]
      [
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [n7QuarticColumnGamma810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnGamma810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * C.natDegree + D.natDegree < d)
    (hd7 : E.natDegree + F.natDegree < d) :
    (n7QuarticColumnGamma810_live_InfraN7c2 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnGamma810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * C.natDegree + D.natDegree < d)
    (hd7 : E.natDegree + F.natDegree < d) :
    (n7QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnGamma810 gamma A B C D E F G = n7QuarticColumnGamma810_live_InfraN7c1 gamma A B C D E F G + n7QuarticColumnGamma810_live_InfraN7c2 gamma A B C D E F G := by
    simp only [n7QuarticColumnGamma810, n7QuarticColumnGamma810_live_InfraN7c1, n7QuarticColumnGamma810_live_InfraN7c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnGamma810_live_InfraN7c1_natDegree_lt gamma A B C D E F G hd0 hd1 hd2 hd3) (n7QuarticColumnGamma810_live_InfraN7c2_natDegree_lt gamma A B C D E F G hd4 hd5 hd6 hd7)))


theorem n7QuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroN7Quartic810` (17 monomials). -/
def n7QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 524288 * delta : k) • A ^ 6
  + (15 / 2048 * delta : k) • (A ^ 4 * C)
  - (15 / 8192 * delta : k) • (A ^ 3 * B ^ 2)
  + (15 / 512 * delta : k) • (A ^ 3 * E)
  - (15 / 1024 * delta : k) • (A ^ 2 * B * D)
  + (5 / 2048 * delta : k) • (A ^ 2 * C ^ 2)
  + (25 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (15 / 128 * delta : k) • (A ^ 2 * G)
  - (5 / 64 * delta : k) • (A * B * F)
  - (5 / 64 * delta : k) • (A * C * E)
  - (5 / 128 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

def n7QuarticColumnDelta810_live_InfraN7c1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 524288 * delta : k) • A ^ 6
  + (15 / 2048 * delta : k) • (A ^ 4 * C)
  - (15 / 8192 * delta : k) • (A ^ 3 * B ^ 2)
  + (15 / 512 * delta : k) • (A ^ 3 * E)
  - (15 / 1024 * delta : k) • (A ^ 2 * B * D)
  + (5 / 2048 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnDelta810_live_InfraN7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnDelta810_live_InfraN7c1
    (delta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnDelta810_live_InfraN7c1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 524288 * delta : k), (15 / 2048 * delta : k), (-(15 / 8192 * delta) : k),
      (15 / 512 * delta : k), (-(15 / 1024 * delta) : k), (5 / 2048 * delta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnDelta810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n7QuarticColumnDelta810_live_InfraN7c1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnDelta810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnDelta810_live_InfraN7c2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (15 / 128 * delta : k) • (A ^ 2 * G)
  - (5 / 64 * delta : k) • (A * B * F)
  - (5 / 64 * delta : k) • (A * C * E)
  - (5 / 128 * delta : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnDelta810_live_InfraN7c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnDelta810_live_InfraN7c2
    (delta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnDelta810_live_InfraN7c2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 1024 * delta : k), (-(135 / 4096 * delta) : k), (15 / 128 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 64 * delta) : k), (-(5 / 128 * delta) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnDelta810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + G.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + 2 * D.natDegree < d) :
    (n7QuarticColumnDelta810_live_InfraN7c2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnDelta810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnDelta810_live_InfraN7c3
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnDelta810_live_InfraN7c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnDelta810_live_InfraN7c3
    (delta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnDelta810_live_InfraN7c3 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 * delta : k), (15 / 32 * delta : k), (5 / 64 * delta : k),
      (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n7QuarticColumnDelta810_live_InfraN7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810_live_InfraN7c3_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd12 : 2 * B.natDegree + E.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 3 * C.natDegree < d)
    (hd15 : D.natDegree + F.natDegree < d)
    (hd16 : 2 * E.natDegree < d) :
    (n7QuarticColumnDelta810_live_InfraN7c3 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnDelta810_live_InfraN7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
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
    (hd15 : D.natDegree + F.natDegree < d)
    (hd16 : 2 * E.natDegree < d) :
    (n7QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnDelta810 delta A B C D E F G = n7QuarticColumnDelta810_live_InfraN7c1 delta A B C D E F G + n7QuarticColumnDelta810_live_InfraN7c2 delta A B C D E F G + n7QuarticColumnDelta810_live_InfraN7c3 delta A B C D E F G := by
    simp only [n7QuarticColumnDelta810, n7QuarticColumnDelta810_live_InfraN7c1, n7QuarticColumnDelta810_live_InfraN7c2, n7QuarticColumnDelta810_live_InfraN7c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnDelta810_live_InfraN7c1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnDelta810_live_InfraN7c2_natDegree_lt delta A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (n7QuarticColumnDelta810_live_InfraN7c3_natDegree_lt delta A B C D E F G hd12 hd13 hd14 hd15 hd16)))


theorem n7QuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroN7Quartic810` (5 monomials). -/
def n7QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnEpsilon810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * epsilon) : k), (7 / 32 * epsilon : k), (1 / 4 * epsilon : k),
      (-(1 / 2 * epsilon) : k), (-(1 / 2 * epsilon) : k)
      ]
      [
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n7QuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (n7QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n7QuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroN7Quartic810` (11 monomials). -/
def n7QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 32768 * zeta : k) • A ^ 5
  + (3 / 128 * zeta : k) • (A ^ 3 * C)
  - (3 / 512 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A ^ 2 * E)
  - (3 / 64 * zeta : k) • (A * B * D)
  - (9 / 128 * zeta : k) • (A * C ^ 2)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

def n7QuarticColumnZeta810_live_InfraN7c1
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 32768 * zeta : k) • A ^ 5
  + (3 / 128 * zeta : k) • (A ^ 3 * C)
  - (3 / 512 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A ^ 2 * E)
  - (3 / 64 * zeta : k) • (A * B * D)
  - (9 / 128 * zeta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnZeta810_live_InfraN7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnZeta810_live_InfraN7c1
    (zeta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnZeta810_live_InfraN7c1 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 32768 * zeta : k), (3 / 128 * zeta : k), (-(3 / 512 * zeta) : k),
      (3 / 32 * zeta : k), (-(3 / 64 * zeta) : k), (-(9 / 128 * zeta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnZeta810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n7QuarticColumnZeta810_live_InfraN7c1 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnZeta810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnZeta810_live_InfraN7c2
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnZeta810_live_InfraN7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnZeta810_live_InfraN7c2
    (zeta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnZeta810_live_InfraN7c2 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 128 * zeta : k), (3 / 8 * zeta : k), (-(3 / 8 * zeta) : k),
      (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnZeta810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd6 : 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + G.natDegree < d)
    (hd8 : B.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + E.natDegree < d)
    (hd10 : 2 * D.natDegree < d) :
    (n7QuarticColumnZeta810_live_InfraN7c2 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnZeta810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
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
    (n7QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnZeta810 zeta A B C D E F G = n7QuarticColumnZeta810_live_InfraN7c1 zeta A B C D E F G + n7QuarticColumnZeta810_live_InfraN7c2 zeta A B C D E F G := by
    simp only [n7QuarticColumnZeta810, n7QuarticColumnZeta810_live_InfraN7c1, n7QuarticColumnZeta810_live_InfraN7c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnZeta810_live_InfraN7c1_natDegree_lt zeta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnZeta810_live_InfraN7c2_natDegree_lt zeta A B C D E F G hd6 hd7 hd8 hd9 hd10)))


theorem n7QuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroN7Quartic810` (4 monomials). -/
def n7QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 16 * eta : k)) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnEta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 16 * eta) : k), (3 / 64 * eta : k), (-(1 / 4 * eta) : k),
      (-(1 / 4 * eta) : k)
      ]
      [
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : B.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + D.natDegree < d) :
    (n7QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n7QuarticColumnEta810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroN7Quartic810` (7 monomials). -/
def n7QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 4096 * theta : k) • A ^ 4
  + (1 / 16 * theta : k) • (A ^ 2 * C)
  - (1 / 64 * theta : k) • (A * B ^ 2)
  + (1 / 4 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

def n7QuarticColumnTheta810_live_InfraN7c1
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 4096 * theta : k) • A ^ 4
  + (1 / 16 * theta : k) • (A ^ 2 * C)
  - (1 / 64 * theta : k) • (A * B ^ 2)
  + (1 / 4 * theta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnTheta810_live_InfraN7c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnTheta810_live_InfraN7c1
    (theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnTheta810_live_InfraN7c1 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 4096 * theta : k), (1 / 16 * theta : k), (-(1 / 64 * theta) : k),
      (1 / 4 * theta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n7QuarticColumnTheta810_live_InfraN7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnTheta810_live_InfraN7c1_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d) :
    (n7QuarticColumnTheta810_live_InfraN7c1 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnTheta810_live_InfraN7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n7QuarticColumnTheta810_live_InfraN7c2
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((1 / 8 * theta : k) • (B * D))
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticColumnTheta810_live_InfraN7c2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN7_n7QuarticColumnTheta810_live_InfraN7c2
    (theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticColumnTheta810_live_InfraN7c2 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k), (1 * theta : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n7QuarticColumnTheta810_live_InfraN7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnTheta810_live_InfraN7c2_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n7QuarticColumnTheta810_live_InfraN7c2 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN7_n7QuarticColumnTheta810_live_InfraN7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n7QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  have hsplit : n7QuarticColumnTheta810 theta A B C D E F G = n7QuarticColumnTheta810_live_InfraN7c1 theta A B C D E F G + n7QuarticColumnTheta810_live_InfraN7c2 theta A B C D E F G := by
    simp only [n7QuarticColumnTheta810, n7QuarticColumnTheta810_live_InfraN7c1, n7QuarticColumnTheta810_live_InfraN7c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n7QuarticColumnTheta810_live_InfraN7c1_natDegree_lt theta A B C D E F G hd0 hd1 hd2 hd3) (n7QuarticColumnTheta810_live_InfraN7c2_natDegree_lt theta A B C D E F G hd4 hd5 hd6)))


theorem n7QuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    n7QuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [n7QuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroN7Quartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroN7Quartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticLoadFree810 A B C D E F G +
      n7QuarticColumnL1810 l A B C D E F G +
      n7QuarticColumnL2810 l A B C D E F G +
      n7QuarticColumnBeta1810 beta A B C D E F G +
      n7QuarticColumnBeta2810 beta A B C D E F G +
      n7QuarticColumnGamma810 gamma A B C D E F G +
      n7QuarticColumnDelta810 delta A B C D E F G +
      n7QuarticColumnEpsilon810 epsilon A B C D E F G +
      n7QuarticColumnZeta810 zeta A B C D E F G +
      n7QuarticColumnEta810 eta A B C D E F G +
      n7QuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroN7Quartic810, n7QuarticLoadFree810, n7QuarticColumnL1810, n7QuarticColumnL2810, n7QuarticColumnBeta1810, n7QuarticColumnBeta2810, n7QuarticColumnGamma810, n7QuarticColumnDelta810, n7QuarticColumnEpsilon810, n7QuarticColumnZeta810, n7QuarticColumnEta810, n7QuarticColumnTheta810, degreeZeroPrimitiveQuartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraN7810

end Max11DegreeRoutes
