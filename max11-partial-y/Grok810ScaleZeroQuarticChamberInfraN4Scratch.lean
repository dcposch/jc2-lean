import Grok810ScaleZeroQuarticChamberAuxTowerScratch

/-! # `N₄` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroN4Quartic810` has 153 monomials.  `…ChamberFacesPart0Scratch` does this
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

section QuarticChamberInfraN4810

/-! ## `N₄`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroN4Quartic810` (33 monomials). -/
def n4QuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 3 * B ^ 2 * D)
  + (155 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (107 / 8192 : k) • (A * B ^ 5)
  - (55 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (95 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (45 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 512 : k) • (A * B ^ 2 * C * D)
  - (15 / 256 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 256 : k) • (A ^ 2 * D * G)
  + (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 32 : k) • (A * B * C * G)
  + (5 / 16 : k) • (A * B * D * F)
  + (5 / 32 : k) • (A * B * E ^ 2)
  + (5 / 64 : k) • (A * C ^ 2 * F)
  + (5 / 16 : k) • (A * C * D * E)
  + (5 / 64 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 8 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN4Quartic810`, chunk 1/2 (20 monomials). -/
def n4QuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8
  + (315 / 4194304 * l : k) • (A ^ 6 * C)
  - (99 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (45 / 131072 * l : k) • (A ^ 5 * E)
  - (117 / 262144 * l : k) • (A ^ 4 * B * D)
  + (459 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (9 / 32768 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (1017 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (9 / 32768 * l : k) • (A ^ 4 * G)
  + (9 / 1024 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (27 / 2048 * l : k) • (A ^ 2 * B ^ 2 * E)
  - (189 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (27 / 512 * l : k) • (A * B ^ 3 * D)
  - (477 / 8192 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 1024 * l : k) • (A ^ 2 * C * G)
  + (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)

def n4QuarticColumnL1810_live_InfraN4c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8
  + (315 / 4194304 * l : k) • (A ^ 6 * C)
  - (99 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (45 / 131072 * l : k) • (A ^ 5 * E)
  - (117 / 262144 * l : k) • (A ^ 4 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810_live_InfraN4c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c1
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810_live_InfraN4c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (495 / 268435456 * l : k), (315 / 4194304 * l : k), (-(99 / 2097152 * l) : k),
      (45 / 131072 * l : k), (-(117 / 262144 * l) : k)
      ]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n4QuarticColumnL1810_live_InfraN4c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnL1810_live_InfraN4c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (459 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (9 / 32768 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (1017 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (9 / 32768 * l : k) • (A ^ 4 * G)
  + (9 / 1024 * l : k) • (A ^ 3 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810_live_InfraN4c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c2
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810_live_InfraN4c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (459 / 524288 * l : k), (-(9 / 32768 * l) : k), (1017 / 262144 * l : k),
      (9 / 32768 * l : k), (9 / 1024 * l : k)
      ]
      [
      [4, 0, 2, 0, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1],
      [3, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd8 : 4 * A.natDegree + G.natDegree < d)
    (hd9 : 3 * A.natDegree + C.natDegree + E.natDegree < d) :
    (n4QuarticColumnL1810_live_InfraN4c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnL1810_live_InfraN4c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 4096 * l : k) • (A ^ 3 * D ^ 2))
  - (27 / 2048 * l : k) • (A ^ 2 * B ^ 2 * E)
  - (189 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (27 / 512 * l : k) • (A * B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810_live_InfraN4c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c3
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810_live_InfraN4c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 4096 * l) : k), (-(27 / 2048 * l) : k), (-(189 / 8192 * l) : k),
      (9 / 16384 * l : k), (-(27 / 512 * l) : k)
      ]
      [
      [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0],
      [1, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810_live_InfraN4c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_live_InfraN4c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd12 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd14 : A.natDegree + 3 * B.natDegree + D.natDegree < d) :
    (n4QuarticColumnL1810_live_InfraN4c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnL1810_live_InfraN4c4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((477 / 8192 * l : k) • (A * B ^ 2 * C ^ 2))
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 1024 * l : k) • (A ^ 2 * C * G)
  + (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810_live_InfraN4c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c4
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810_live_InfraN4c4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(477 / 8192 * l) : k), (-(567 / 16384 * l) : k), (9 / 1024 * l : k),
      (9 / 512 * l : k), (27 / 1024 * l : k)
      ]
      [
      [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0],
      [2, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810_live_InfraN4c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_live_InfraN4c4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd16 : 4 * B.natDegree + C.natDegree < d)
    (hd17 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd18 : 2 * A.natDegree + D.natDegree + F.natDegree < d)
    (hd19 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810_live_InfraN4c4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL1810_live_InfraN4c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_natDegree_lt
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
    (hd9 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd12 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd14 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd15 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd16 : 4 * B.natDegree + C.natDegree < d)
    (hd17 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd18 : 2 * A.natDegree + D.natDegree + F.natDegree < d)
    (hd19 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnL1810 l A B C D E F G = n4QuarticColumnL1810_live_InfraN4c1 l A B C D E F G + n4QuarticColumnL1810_live_InfraN4c2 l A B C D E F G + n4QuarticColumnL1810_live_InfraN4c3 l A B C D E F G + n4QuarticColumnL1810_live_InfraN4c4 l A B C D E F G := by
    simp only [n4QuarticColumnL1810, n4QuarticColumnL1810_live_InfraN4c1, n4QuarticColumnL1810_live_InfraN4c2, n4QuarticColumnL1810_live_InfraN4c3, n4QuarticColumnL1810_live_InfraN4c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnL1810_live_InfraN4c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (n4QuarticColumnL1810_live_InfraN4c2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n4QuarticColumnL1810_live_InfraN4c3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n4QuarticColumnL1810_live_InfraN4c4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem n4QuarticColumnL1810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN4Quartic810`, chunk 2/2 (18 monomials). -/
def n4QuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 256 * l : k) • (A * B ^ 2 * G)
  + (27 / 256 * l : k) • (A * B * C * F)
  + (45 / 256 * l : k) • (A * B * D * E)
  + (27 / 512 * l : k) • (A * C ^ 2 * E)
  + (45 / 512 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  - (27 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

def n4QuarticColumnL2810_live_InfraN4c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 256 * l : k) • (A * B ^ 2 * G)
  + (27 / 256 * l : k) • (A * B * C * F)
  + (45 / 256 * l : k) • (A * B * D * E)
  + (27 / 512 * l : k) • (A * C ^ 2 * E)
  + (45 / 512 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810_live_InfraN4c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL2810_live_InfraN4c1
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810_live_InfraN4c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 256 * l : k), (27 / 256 * l : k), (45 / 256 * l : k),
      (27 / 512 * l : k), (45 / 512 * l : k), (27 / 512 * l : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [n4QuarticColumnL2810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d) :
    (n4QuarticColumnL2810_live_InfraN4c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL2810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnL2810_live_InfraN4c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  - (27 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810_live_InfraN4c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL2810_live_InfraN4c2
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810_live_InfraN4c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 256 * l : k), (45 / 512 * l : k), (189 / 1024 * l : k),
      (63 / 4096 * l : k), (-(27 / 128 * l) : k), (-(9 / 64 * l) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1]
      ] := by
  simp only [n4QuarticColumnL2810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + D.natDegree + G.natDegree < d) :
    (n4QuarticColumnL2810_live_InfraN4c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL2810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnL2810_live_InfraN4c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 32 * l : k) • (B * E * F))
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810_live_InfraN4c3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnL2810_live_InfraN4c3
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810_live_InfraN4c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 32 * l) : k), (-(9 / 128 * l) : k), (-(9 / 32 * l) : k),
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k), (9 / 16 * l : k)
      ]
      [
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [n4QuarticColumnL2810_live_InfraN4c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_live_InfraN4c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd12 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd13 : 2 * C.natDegree + G.natDegree < d)
    (hd14 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + 2 * E.natDegree < d)
    (hd16 : 2 * D.natDegree + E.natDegree < d)
    (hd17 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810_live_InfraN4c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnL2810_live_InfraN4c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd12 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd13 : 2 * C.natDegree + G.natDegree < d)
    (hd14 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + 2 * E.natDegree < d)
    (hd16 : 2 * D.natDegree + E.natDegree < d)
    (hd17 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnL2810 l A B C D E F G = n4QuarticColumnL2810_live_InfraN4c1 l A B C D E F G + n4QuarticColumnL2810_live_InfraN4c2 l A B C D E F G + n4QuarticColumnL2810_live_InfraN4c3 l A B C D E F G := by
    simp only [n4QuarticColumnL2810, n4QuarticColumnL2810_live_InfraN4c1, n4QuarticColumnL2810_live_InfraN4c2, n4QuarticColumnL2810_live_InfraN4c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnL2810_live_InfraN4c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL2810_live_InfraN4c2_natDegree_lt l A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (n4QuarticColumnL2810_live_InfraN4c3_natDegree_lt l A B C D E F G hd12 hd13 hd14 hd15 hd16 hd17)))


theorem n4QuarticColumnL2810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN4Quartic810`, chunk 1/2 (20 monomials). -/
def n4QuarticColumnBeta1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7
  + (35 / 131072 * beta : k) • (A ^ 5 * C)
  - (49 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (21 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 4096 * beta : k) • (A ^ 3 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 3 * C ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (427 / 32768 * beta : k) • (A * B ^ 4)
  + (7 / 256 * beta : k) • (A ^ 2 * C * E)
  - (7 / 256 * beta : k) • (A ^ 2 * D ^ 2)
  - (77 / 1024 * beta : k) • (A * B ^ 2 * E)
  - (35 / 256 * beta : k) • (A * B * C * D)
  - (7 / 512 * beta : k) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * D * F)
  + (21 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

def n4QuarticColumnBeta1810_live_InfraN4c1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7
  + (35 / 131072 * beta : k) • (A ^ 5 * C)
  - (49 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (21 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 4096 * beta : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810_live_InfraN4c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c1
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810_live_InfraN4c1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 2097152 * beta : k), (35 / 131072 * beta : k), (-(49 / 262144 * beta) : k),
      (21 / 16384 * beta : k), (-(7 / 4096 * beta) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n4QuarticColumnBeta1810_live_InfraN4c1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnBeta1810_live_InfraN4c2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 8192 * beta : k) • (A ^ 3 * C ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (427 / 32768 * beta : k) • (A * B ^ 4)
  + (7 / 256 * beta : k) • (A ^ 2 * C * E)
  - (7 / 256 * beta : k) • (A ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810_live_InfraN4c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c2
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810_live_InfraN4c2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 8192 * beta : k), (35 / 4096 * beta : k), (427 / 32768 * beta : k),
      (7 / 256 * beta : k), (-(7 / 256 * beta) : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * A.natDegree + 2 * D.natDegree < d) :
    (n4QuarticColumnBeta1810_live_InfraN4c2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnBeta1810_live_InfraN4c3
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((77 / 1024 * beta : k) • (A * B ^ 2 * E))
  - (35 / 256 * beta : k) • (A * B * C * D)
  - (7 / 512 * beta : k) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810_live_InfraN4c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c3
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810_live_InfraN4c3 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(77 / 1024 * beta) : k), (-(35 / 256 * beta) : k), (-(7 / 512 * beta) : k),
      (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810_live_InfraN4c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_live_InfraN4c3_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd10 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 3 * C.natDegree < d)
    (hd13 : 3 * B.natDegree + D.natDegree < d)
    (hd14 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnBeta1810_live_InfraN4c3 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnBeta1810_live_InfraN4c4
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (A * D * F)
  + (21 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810_live_InfraN4c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c4
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810_live_InfraN4c4 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 64 * beta : k), (21 / 128 * beta : k), (7 / 32 * beta : k),
      (7 / 32 * beta : k), (7 / 64 * beta : k)
      ]
      [
      [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 2, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810_live_InfraN4c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_live_InfraN4c4_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : A.natDegree + 2 * E.natDegree < d)
    (hd17 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd18 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd19 : 2 * C.natDegree + E.natDegree < d) :
    (n4QuarticColumnBeta1810_live_InfraN4c4 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta1810_live_InfraN4c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_natDegree_lt
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
    (hd8 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd10 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 3 * C.natDegree < d)
    (hd13 : 3 * B.natDegree + D.natDegree < d)
    (hd14 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd15 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : A.natDegree + 2 * E.natDegree < d)
    (hd17 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd18 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd19 : 2 * C.natDegree + E.natDegree < d) :
    (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnBeta1810 beta A B C D E F G = n4QuarticColumnBeta1810_live_InfraN4c1 beta A B C D E F G + n4QuarticColumnBeta1810_live_InfraN4c2 beta A B C D E F G + n4QuarticColumnBeta1810_live_InfraN4c3 beta A B C D E F G + n4QuarticColumnBeta1810_live_InfraN4c4 beta A B C D E F G := by
    simp only [n4QuarticColumnBeta1810, n4QuarticColumnBeta1810_live_InfraN4c1, n4QuarticColumnBeta1810_live_InfraN4c2, n4QuarticColumnBeta1810_live_InfraN4c3, n4QuarticColumnBeta1810_live_InfraN4c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnBeta1810_live_InfraN4c1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n4QuarticColumnBeta1810_live_InfraN4c2_natDegree_lt beta A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n4QuarticColumnBeta1810_live_InfraN4c3_natDegree_lt beta A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n4QuarticColumnBeta1810_live_InfraN4c4_natDegree_lt beta A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem n4QuarticColumnBeta1810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnBeta1810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN4Quartic810`, chunk 2/2 (2 monomials). -/
def n4QuarticColumnBeta2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 64 * beta : k), (-(7 / 16 * beta) : k)
      ]
      [
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n4QuarticColumnBeta2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnBeta2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n4QuarticColumnBeta2810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnBeta2810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnBeta2810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroN4Quartic810` (12 monomials). -/
def n4QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  - (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 64 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 32 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  + (3 / 8 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

def n4QuarticColumnGamma810_live_InfraN4c1
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  - (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 64 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 32 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnGamma810_live_InfraN4c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnGamma810_live_InfraN4c1
    (gamma : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnGamma810_live_InfraN4c1 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 2048 * gamma : k), (-(3 / 256 * gamma) : k), (-(3 / 256 * gamma) : k),
      (-(9 / 64 * gamma) : k), (-(3 / 32 * gamma) : k), (-(27 / 256 * gamma) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnGamma810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * B.natDegree + C.natDegree < d) :
    (n4QuarticColumnGamma810_live_InfraN4c1 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnGamma810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnGamma810_live_InfraN4c2
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnGamma810_live_InfraN4c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnGamma810_live_InfraN4c2
    (gamma : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnGamma810_live_InfraN4c2 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * gamma : k), (9 / 64 * gamma : k), (3 / 8 * gamma : k),
      (3 / 16 * gamma : k), (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k)
      ]
      [
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [n4QuarticColumnGamma810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd6 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : B.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * C.natDegree + D.natDegree < d)
    (hd11 : E.natDegree + F.natDegree < d) :
    (n4QuarticColumnGamma810_live_InfraN4c2 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnGamma810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : B.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * C.natDegree + D.natDegree < d)
    (hd11 : E.natDegree + F.natDegree < d) :
    (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnGamma810 gamma A B C D E F G = n4QuarticColumnGamma810_live_InfraN4c1 gamma A B C D E F G + n4QuarticColumnGamma810_live_InfraN4c2 gamma A B C D E F G := by
    simp only [n4QuarticColumnGamma810, n4QuarticColumnGamma810_live_InfraN4c1, n4QuarticColumnGamma810_live_InfraN4c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnGamma810_live_InfraN4c1_natDegree_lt gamma A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnGamma810_live_InfraN4c2_natDegree_lt gamma A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11)))


theorem n4QuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroN4Quartic810` (16 monomials). -/
def n4QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6
  + (15 / 16384 * delta : k) • (A ^ 4 * C)
  - (5 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (25 / 512 * delta : k) • (A ^ 2 * B * D)
  + (5 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (155 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * B * F)
  + (15 / 64 * delta : k) • (A * C * E)
  + (25 / 128 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

def n4QuarticColumnDelta810_live_InfraN4c1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6
  + (15 / 16384 * delta : k) • (A ^ 4 * C)
  - (5 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (25 / 512 * delta : k) • (A ^ 2 * B * D)
  + (5 / 1024 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810_live_InfraN4c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnDelta810_live_InfraN4c1
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810_live_InfraN4c1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 262144 * delta : k), (15 / 16384 * delta : k), (-(5 / 16384 * delta) : k),
      (5 / 1024 * delta : k), (-(25 / 512 * delta) : k), (5 / 1024 * delta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnDelta810_live_InfraN4c1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnDelta810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnDelta810_live_InfraN4c2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((155 / 1024 * delta : k) • (A * B ^ 2 * C))
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * B * F)
  + (15 / 64 * delta : k) • (A * C * E)
  + (25 / 128 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810_live_InfraN4c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnDelta810_live_InfraN4c2
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810_live_InfraN4c2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(155 / 1024 * delta) : k), (-(135 / 4096 * delta) : k), (5 / 64 * delta : k),
      (15 / 64 * delta : k), (25 / 128 * delta : k), (25 / 128 * delta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d) :
    (n4QuarticColumnDelta810_live_InfraN4c2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnDelta810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnDelta810_live_InfraN4c3
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810_live_InfraN4c3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnDelta810_live_InfraN4c3
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810_live_InfraN4c3 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 32 * delta : k), (5 / 64 * delta : k), (-(5 / 8 * delta) : k),
      (-(5 / 16 * delta) : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810_live_InfraN4c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_live_InfraN4c3_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810_live_InfraN4c3 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnDelta810_live_InfraN4c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_natDegree_lt
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
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnDelta810 delta A B C D E F G = n4QuarticColumnDelta810_live_InfraN4c1 delta A B C D E F G + n4QuarticColumnDelta810_live_InfraN4c2 delta A B C D E F G + n4QuarticColumnDelta810_live_InfraN4c3 delta A B C D E F G := by
    simp only [n4QuarticColumnDelta810, n4QuarticColumnDelta810_live_InfraN4c1, n4QuarticColumnDelta810_live_InfraN4c2, n4QuarticColumnDelta810_live_InfraN4c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnDelta810_live_InfraN4c1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnDelta810_live_InfraN4c2_natDegree_lt delta A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (n4QuarticColumnDelta810_live_InfraN4c3_natDegree_lt delta A B C D E F G hd12 hd13 hd14 hd15)))


theorem n4QuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroN4Quartic810` (9 monomials). -/
def n4QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 64 * epsilon : k)) • (A ^ 2 * B * C)
  - (1 / 16 * epsilon : k) • (A * B ^ 3)
  + (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 4 * epsilon : k) • (A * B * E)
  + (1 / 4 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

def n4QuarticColumnEpsilon810_live_InfraN4c1
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 64 * epsilon : k)) • (A ^ 2 * B * C)
  - (1 / 16 * epsilon : k) • (A * B ^ 3)
  + (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 4 * epsilon : k) • (A * B * E)
  + (1 / 4 * epsilon : k) • (A * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEpsilon810_live_InfraN4c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnEpsilon810_live_InfraN4c1
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810_live_InfraN4c1 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 64 * epsilon) : k), (-(1 / 16 * epsilon) : k), (1 / 32 * epsilon : k),
      (1 / 4 * epsilon : k), (1 / 4 * epsilon : k)
      ]
      [
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnEpsilon810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d) :
    (n4QuarticColumnEpsilon810_live_InfraN4c1 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnEpsilon810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnEpsilon810_live_InfraN4c2
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEpsilon810_live_InfraN4c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnEpsilon810_live_InfraN4c2
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810_live_InfraN4c2 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 32 * epsilon : k), (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 / 2 * epsilon) : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnEpsilon810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree < d)
    (hd7 : C.natDegree + F.natDegree < d)
    (hd8 : D.natDegree + E.natDegree < d) :
    (n4QuarticColumnEpsilon810_live_InfraN4c2 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnEpsilon810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree < d)
    (hd7 : C.natDegree + F.natDegree < d)
    (hd8 : D.natDegree + E.natDegree < d) :
    (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnEpsilon810 epsilon A B C D E F G = n4QuarticColumnEpsilon810_live_InfraN4c1 epsilon A B C D E F G + n4QuarticColumnEpsilon810_live_InfraN4c2 epsilon A B C D E F G := by
    simp only [n4QuarticColumnEpsilon810, n4QuarticColumnEpsilon810_live_InfraN4c1, n4QuarticColumnEpsilon810_live_InfraN4c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnEpsilon810_live_InfraN4c1_natDegree_lt epsilon A B C D E F G hd0 hd1 hd2 hd3 hd4) (n4QuarticColumnEpsilon810_live_InfraN4c2_natDegree_lt epsilon A B C D E F G hd5 hd6 hd7 hd8)))


theorem n4QuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroN4Quartic810` (11 monomials). -/
def n4QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5
  + (3 / 1024 * zeta : k) • (A ^ 3 * C)
  - (39 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (15 / 64 * zeta : k) • (A * B * D)
  + (9 / 128 * zeta : k) • (A * C ^ 2)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

def n4QuarticColumnZeta810_live_InfraN4c1
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5
  + (3 / 1024 * zeta : k) • (A ^ 3 * C)
  - (39 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (15 / 64 * zeta : k) • (A * B * D)
  + (9 / 128 * zeta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnZeta810_live_InfraN4c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnZeta810_live_InfraN4c1
    (zeta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810_live_InfraN4c1 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32768 * zeta : k), (3 / 1024 * zeta : k), (-(39 / 2048 * zeta) : k),
      (3 / 128 * zeta : k), (15 / 64 * zeta : k), (9 / 128 * zeta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnZeta810_live_InfraN4c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_live_InfraN4c1_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnZeta810_live_InfraN4c1 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnZeta810_live_InfraN4c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n4QuarticColumnZeta810_live_InfraN4c2
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnZeta810_live_InfraN4c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnZeta810_live_InfraN4c2
    (zeta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810_live_InfraN4c2 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k),
      (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnZeta810_live_InfraN4c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_live_InfraN4c2_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd6 : 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + G.natDegree < d)
    (hd8 : B.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + E.natDegree < d)
    (hd10 : 2 * D.natDegree < d) :
    (n4QuarticColumnZeta810_live_InfraN4c2 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnZeta810_live_InfraN4c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_natDegree_lt
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
    (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  have hsplit : n4QuarticColumnZeta810 zeta A B C D E F G = n4QuarticColumnZeta810_live_InfraN4c1 zeta A B C D E F G + n4QuarticColumnZeta810_live_InfraN4c2 zeta A B C D E F G := by
    simp only [n4QuarticColumnZeta810, n4QuarticColumnZeta810_live_InfraN4c1, n4QuarticColumnZeta810_live_InfraN4c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n4QuarticColumnZeta810_live_InfraN4c1_natDegree_lt zeta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnZeta810_live_InfraN4c2_natDegree_lt zeta A B C D E F G hd6 hd7 hd8 hd9 hd10)))


theorem n4QuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroN4Quartic810` (6 monomials). -/
def n4QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 8 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 2 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 64 * eta : k), (1 / 8 * eta : k), (3 / 64 * eta : k),
      (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k)
      ]
      [
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : A.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + D.natDegree < d) :
    (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n4QuarticColumnEta810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroN4Quartic810` (6 monomials). -/
def n4QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4096 * theta : k) • A ^ 4
  + (1 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 32 * theta : k) • (A * B ^ 2)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnTheta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN4_n4QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4096 * theta : k), (1 / 128 * theta : k), (1 / 32 * theta : k),
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k), (1 * theta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n4QuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN4_n4QuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n4QuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroN4Quartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroN4Quartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticLoadFree810 A B C D E F G +
      n4QuarticColumnL1810 l A B C D E F G +
      n4QuarticColumnL2810 l A B C D E F G +
      n4QuarticColumnBeta1810 beta A B C D E F G +
      n4QuarticColumnBeta2810 beta A B C D E F G +
      n4QuarticColumnGamma810 gamma A B C D E F G +
      n4QuarticColumnDelta810 delta A B C D E F G +
      n4QuarticColumnEpsilon810 epsilon A B C D E F G +
      n4QuarticColumnZeta810 zeta A B C D E F G +
      n4QuarticColumnEta810 eta A B C D E F G +
      n4QuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroN4Quartic810, n4QuarticLoadFree810, n4QuarticColumnL1810, n4QuarticColumnL2810, n4QuarticColumnBeta1810, n4QuarticColumnBeta2810, n4QuarticColumnGamma810, n4QuarticColumnDelta810, n4QuarticColumnEpsilon810, n4QuarticColumnZeta810, n4QuarticColumnEta810, n4QuarticColumnTheta810, degreeZeroPrimitiveQuartic810, degreeZeroOmicronQuartic810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraN4810

end Max11DegreeRoutes
