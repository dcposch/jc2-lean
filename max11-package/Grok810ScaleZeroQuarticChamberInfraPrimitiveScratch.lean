import Grok810ScaleZeroQuarticDefsScratch

/-! # `Π` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroPrimitiveQuartic810` has 160 monomials.  `…ChamberFacesPart0Scratch` does this
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

section QuarticChamberInfraPrimitive810

/-! ## `Π`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroPrimitiveQuartic810` (37 monomials). -/
def primitiveQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroPrimitiveQuartic810`, chunk 1/2 (20 monomials). -/
def primitiveQuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)

def primitiveQuarticColumnL1810_live_InfraPrimitivec1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec1
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810_live_InfraPrimitivec1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1575 / 268435456 * l : k), (765 / 4194304 * l : k), (-(369 / 4194304 * l) : k),
      (171 / 262144 * l : k), (-(153 / 262144 * l) : k)
      ]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL1810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnL1810_live_InfraPrimitivec1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnL1810_live_InfraPrimitivec2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810_live_InfraPrimitivec2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec2
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810_live_InfraPrimitivec2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (855 / 524288 * l : k), (-(81 / 131072 * l) : k), (261 / 262144 * l : k),
      (45 / 32768 * l : k), (-(9 / 4096 * l) : k)
      ]
      [
      [4, 0, 2, 0, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1],
      [3, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [primitiveQuarticColumnL1810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd8 : 4 * A.natDegree + G.natDegree < d)
    (hd9 : 3 * A.natDegree + B.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnL1810_live_InfraPrimitivec2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnL1810_live_InfraPrimitivec3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810_live_InfraPrimitivec3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec3
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810_live_InfraPrimitivec3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (99 / 8192 * l : k), (-(9 / 4096 * l) : k), (-(9 / 4096 * l) : k),
      (9 / 8192 * l : k), (27 / 16384 * l : k)
      ]
      [
      [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL1810_live_InfraPrimitivec3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_live_InfraPrimitivec3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 3 * C.natDegree < d) :
    (primitiveQuarticColumnL1810_live_InfraPrimitivec3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnL1810_live_InfraPrimitivec4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((243 / 8192 * l : k) • (A * B ^ 3 * D))
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810_live_InfraPrimitivec4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec4
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810_live_InfraPrimitivec4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(243 / 8192 * l) : k), (-(387 / 16384 * l) : k), (-(567 / 16384 * l) : k),
      (27 / 1024 * l : k), (-(9 / 512 * l) : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1],
      [2, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [primitiveQuarticColumnL1810_live_InfraPrimitivec4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_live_InfraPrimitivec4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd16 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : 4 * B.natDegree + C.natDegree < d)
    (hd18 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd19 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnL1810_live_InfraPrimitivec4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL1810_live_InfraPrimitivec4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_natDegree_lt
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
    (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnL1810 l A B C D E F G = primitiveQuarticColumnL1810_live_InfraPrimitivec1 l A B C D E F G + primitiveQuarticColumnL1810_live_InfraPrimitivec2 l A B C D E F G + primitiveQuarticColumnL1810_live_InfraPrimitivec3 l A B C D E F G + primitiveQuarticColumnL1810_live_InfraPrimitivec4 l A B C D E F G := by
    simp only [primitiveQuarticColumnL1810, primitiveQuarticColumnL1810_live_InfraPrimitivec1, primitiveQuarticColumnL1810_live_InfraPrimitivec2, primitiveQuarticColumnL1810_live_InfraPrimitivec3, primitiveQuarticColumnL1810_live_InfraPrimitivec4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnL1810_live_InfraPrimitivec1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnL1810_live_InfraPrimitivec2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (primitiveQuarticColumnL1810_live_InfraPrimitivec3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (primitiveQuarticColumnL1810_live_InfraPrimitivec4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem primitiveQuarticColumnL1810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroPrimitiveQuartic810`, chunk 2/2 (20 monomials). -/
def primitiveQuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

def primitiveQuarticColumnL2810_live_InfraPrimitivec1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec1
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810_live_InfraPrimitivec1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 1024 * l : k), (9 / 1024 * l : k), (9 / 256 * l : k),
      (45 / 512 * l : k), (9 / 1024 * l : k)
      ]
      [
      [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 2, 0, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL2810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnL2810_live_InfraPrimitivec1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnL2810_live_InfraPrimitivec2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810_live_InfraPrimitivec2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec2
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810_live_InfraPrimitivec2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 256 * l : k), (27 / 512 * l : k), (45 / 256 * l : k),
      (45 / 512 * l : k), (189 / 1024 * l : k)
      ]
      [
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL2810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnL2810_live_InfraPrimitivec2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnL2810_live_InfraPrimitivec3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810_live_InfraPrimitivec3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec3
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810_live_InfraPrimitivec3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 4096 * l : k), (9 / 64 * l : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k)
      ]
      [
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0]
      ] := by
  simp only [primitiveQuarticColumnL2810_live_InfraPrimitivec3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_live_InfraPrimitivec3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 4 * C.natDegree < d)
    (hd11 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnL2810_live_InfraPrimitivec3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnL2810_live_InfraPrimitivec4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 128 * l : k) • (C ^ 2 * G))
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810_live_InfraPrimitivec4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec4
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810_live_InfraPrimitivec4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * l) : k), (-(9 / 32 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (9 / 16 * l : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [primitiveQuarticColumnL2810_live_InfraPrimitivec4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_live_InfraPrimitivec4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : 2 * C.natDegree + G.natDegree < d)
    (hd16 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd17 : C.natDegree + 2 * E.natDegree < d)
    (hd18 : 2 * D.natDegree + E.natDegree < d)
    (hd19 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810_live_InfraPrimitivec4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnL2810_live_InfraPrimitivec4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : 4 * C.natDegree < d)
    (hd11 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : 2 * C.natDegree + G.natDegree < d)
    (hd16 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd17 : C.natDegree + 2 * E.natDegree < d)
    (hd18 : 2 * D.natDegree + E.natDegree < d)
    (hd19 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnL2810 l A B C D E F G = primitiveQuarticColumnL2810_live_InfraPrimitivec1 l A B C D E F G + primitiveQuarticColumnL2810_live_InfraPrimitivec2 l A B C D E F G + primitiveQuarticColumnL2810_live_InfraPrimitivec3 l A B C D E F G + primitiveQuarticColumnL2810_live_InfraPrimitivec4 l A B C D E F G := by
    simp only [primitiveQuarticColumnL2810, primitiveQuarticColumnL2810_live_InfraPrimitivec1, primitiveQuarticColumnL2810_live_InfraPrimitivec2, primitiveQuarticColumnL2810_live_InfraPrimitivec3, primitiveQuarticColumnL2810_live_InfraPrimitivec4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnL2810_live_InfraPrimitivec1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnL2810_live_InfraPrimitivec2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (primitiveQuarticColumnL2810_live_InfraPrimitivec3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (primitiveQuarticColumnL2810_live_InfraPrimitivec4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem primitiveQuarticColumnL2810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroPrimitiveQuartic810` (20 monomials). -/
def primitiveQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2

def primitiveQuarticColumnBeta810_live_InfraPrimitivec1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec1
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810_live_InfraPrimitivec1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 1048576 * beta : k), (21 / 32768 * beta : k), (-(119 / 262144 * beta) : k),
      (35 / 16384 * beta : k), (-(7 / 2048 * beta) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnBeta810_live_InfraPrimitivec1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnBeta810_live_InfraPrimitivec2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810_live_InfraPrimitivec2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec2
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810_live_InfraPrimitivec2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 4096 * beta : k), (-(21 / 8192 * beta) : k), (119 / 16384 * beta : k),
      (21 / 512 * beta : k), (-(7 / 512 * beta) : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * A.natDegree + 2 * D.natDegree < d) :
    (primitiveQuarticColumnBeta810_live_InfraPrimitivec2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnBeta810_live_InfraPrimitivec3
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((21 / 512 * beta : k) • (A * B ^ 2 * E))
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810_live_InfraPrimitivec3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec3
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810_live_InfraPrimitivec3 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(21 / 512 * beta) : k), (-(7 / 128 * beta) : k), (-(7 / 128 * beta) : k),
      (-(91 / 1024 * beta) : k), (7 / 64 * beta : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810_live_InfraPrimitivec3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_live_InfraPrimitivec3_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd10 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * B.natDegree + D.natDegree < d)
    (hd13 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd14 : A.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticColumnBeta810_live_InfraPrimitivec3 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnBeta810_live_InfraPrimitivec4
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810_live_InfraPrimitivec4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec4
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810_live_InfraPrimitivec4 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 32 * beta : k), (7 / 32 * beta : k), (7 / 64 * beta : k),
      (7 / 64 * beta : k), (-(7 / 16 * beta) : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810_live_InfraPrimitivec4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_live_InfraPrimitivec4_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd15 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd16 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd17 : 2 * C.natDegree + E.natDegree < d)
    (hd18 : C.natDegree + 2 * D.natDegree < d)
    (hd19 : 2 * F.natDegree < d) :
    (primitiveQuarticColumnBeta810_live_InfraPrimitivec4 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnBeta810_live_InfraPrimitivec4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_natDegree_lt
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
    (hd12 : 3 * B.natDegree + D.natDegree < d)
    (hd13 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd14 : A.natDegree + 2 * E.natDegree < d)
    (hd15 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd16 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd17 : 2 * C.natDegree + E.natDegree < d)
    (hd18 : C.natDegree + 2 * D.natDegree < d)
    (hd19 : 2 * F.natDegree < d) :
    (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnBeta810 beta A B C D E F G = primitiveQuarticColumnBeta810_live_InfraPrimitivec1 beta A B C D E F G + primitiveQuarticColumnBeta810_live_InfraPrimitivec2 beta A B C D E F G + primitiveQuarticColumnBeta810_live_InfraPrimitivec3 beta A B C D E F G + primitiveQuarticColumnBeta810_live_InfraPrimitivec4 beta A B C D E F G := by
    simp only [primitiveQuarticColumnBeta810, primitiveQuarticColumnBeta810_live_InfraPrimitivec1, primitiveQuarticColumnBeta810_live_InfraPrimitivec2, primitiveQuarticColumnBeta810_live_InfraPrimitivec3, primitiveQuarticColumnBeta810_live_InfraPrimitivec4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnBeta810_live_InfraPrimitivec1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnBeta810_live_InfraPrimitivec2_natDegree_lt beta A B C D E F G hd5 hd6 hd7 hd8 hd9))) (primitiveQuarticColumnBeta810_live_InfraPrimitivec3_natDegree_lt beta A B C D E F G hd10 hd11 hd12 hd13 hd14))) (primitiveQuarticColumnBeta810_live_InfraPrimitivec4_natDegree_lt beta A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem primitiveQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroPrimitiveQuartic810` (15 monomials). -/
def primitiveQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

def primitiveQuarticColumnGamma810_live_InfraPrimitivec1
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnGamma810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnGamma810_live_InfraPrimitivec1
    (gamma : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnGamma810_live_InfraPrimitivec1 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 2048 * gamma : k), (3 / 2048 * gamma : k), (-(3 / 512 * gamma) : k),
      (3 / 256 * gamma : k), (3 / 256 * gamma : k)
      ]
      [
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnGamma810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnGamma810_live_InfraPrimitivec1 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnGamma810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnGamma810_live_InfraPrimitivec2
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 128 * gamma : k) • (A * B ^ 2 * D))
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnGamma810_live_InfraPrimitivec2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnGamma810_live_InfraPrimitivec2
    (gamma : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnGamma810_live_InfraPrimitivec2 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * gamma) : k), (-(3 / 128 * gamma) : k), (-(27 / 256 * gamma) : k),
      (-(3 / 32 * gamma) : k), (3 / 16 * gamma : k)
      ]
      [
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnGamma810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd5 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd7 : 3 * B.natDegree + C.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + D.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnGamma810_live_InfraPrimitivec2 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnGamma810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnGamma810_live_InfraPrimitivec3
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnGamma810_live_InfraPrimitivec3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnGamma810_live_InfraPrimitivec3
    (gamma : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnGamma810_live_InfraPrimitivec3 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * gamma : k), (3 / 8 * gamma : k), (3 / 16 * gamma : k),
      (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k)
      ]
      [
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [primitiveQuarticColumnGamma810_live_InfraPrimitivec3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_live_InfraPrimitivec3_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * B.natDegree + F.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + 2 * D.natDegree < d)
    (hd13 : 2 * C.natDegree + D.natDegree < d)
    (hd14 : E.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnGamma810_live_InfraPrimitivec3 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnGamma810_live_InfraPrimitivec3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd7 : 3 * B.natDegree + C.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + F.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + 2 * D.natDegree < d)
    (hd13 : 2 * C.natDegree + D.natDegree < d)
    (hd14 : E.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnGamma810 gamma A B C D E F G = primitiveQuarticColumnGamma810_live_InfraPrimitivec1 gamma A B C D E F G + primitiveQuarticColumnGamma810_live_InfraPrimitivec2 gamma A B C D E F G + primitiveQuarticColumnGamma810_live_InfraPrimitivec3 gamma A B C D E F G := by
    simp only [primitiveQuarticColumnGamma810, primitiveQuarticColumnGamma810_live_InfraPrimitivec1, primitiveQuarticColumnGamma810_live_InfraPrimitivec2, primitiveQuarticColumnGamma810_live_InfraPrimitivec3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnGamma810_live_InfraPrimitivec1_natDegree_lt gamma A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnGamma810_live_InfraPrimitivec2_natDegree_lt gamma A B C D E F G hd5 hd6 hd7 hd8 hd9))) (primitiveQuarticColumnGamma810_live_InfraPrimitivec3_natDegree_lt gamma A B C D E F G hd10 hd11 hd12 hd13 hd14)))


theorem primitiveQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroPrimitiveQuartic810` (15 monomials). -/
def primitiveQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

def primitiveQuarticColumnDelta810_live_InfraPrimitivec1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnDelta810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnDelta810_live_InfraPrimitivec1
    (delta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810_live_InfraPrimitivec1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 262144 * delta : k), (35 / 16384 * delta : k), (-(25 / 16384 * delta) : k),
      (5 / 1024 * delta : k), (-(5 / 512 * delta) : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnDelta810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnDelta810_live_InfraPrimitivec1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnDelta810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnDelta810_live_InfraPrimitivec2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnDelta810_live_InfraPrimitivec2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnDelta810_live_InfraPrimitivec2
    (delta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810_live_InfraPrimitivec2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 1024 * delta : k), (-(65 / 1024 * delta) : k), (-(135 / 4096 * delta) : k),
      (5 / 64 * delta : k), (5 / 64 * delta : k)
      ]
      [
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnDelta810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d) :
    (primitiveQuarticColumnDelta810_live_InfraPrimitivec2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnDelta810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnDelta810_live_InfraPrimitivec3
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnDelta810_live_InfraPrimitivec3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnDelta810_live_InfraPrimitivec3
    (delta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810_live_InfraPrimitivec3 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 * delta : k), (15 / 32 * delta : k), (5 / 64 * delta : k),
      (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnDelta810_live_InfraPrimitivec3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_live_InfraPrimitivec3_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : D.natDegree + F.natDegree < d)
    (hd14 : 2 * E.natDegree < d) :
    (primitiveQuarticColumnDelta810_live_InfraPrimitivec3 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnDelta810_live_InfraPrimitivec3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_natDegree_lt
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
    (hd8 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : D.natDegree + F.natDegree < d)
    (hd14 : 2 * E.natDegree < d) :
    (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnDelta810 delta A B C D E F G = primitiveQuarticColumnDelta810_live_InfraPrimitivec1 delta A B C D E F G + primitiveQuarticColumnDelta810_live_InfraPrimitivec2 delta A B C D E F G + primitiveQuarticColumnDelta810_live_InfraPrimitivec3 delta A B C D E F G := by
    simp only [primitiveQuarticColumnDelta810, primitiveQuarticColumnDelta810_live_InfraPrimitivec1, primitiveQuarticColumnDelta810_live_InfraPrimitivec2, primitiveQuarticColumnDelta810_live_InfraPrimitivec3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnDelta810_live_InfraPrimitivec1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnDelta810_live_InfraPrimitivec2_natDegree_lt delta A B C D E F G hd5 hd6 hd7 hd8 hd9))) (primitiveQuarticColumnDelta810_live_InfraPrimitivec3_natDegree_lt delta A B C D E F G hd10 hd11 hd12 hd13 hd14)))


theorem primitiveQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroPrimitiveQuartic810` (10 monomials). -/
def primitiveQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 256 * epsilon : k)) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

def primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 256 * epsilon : k)) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1
    (epsilon : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 256 * epsilon) : k), (1 / 64 * epsilon : k), (-(1 / 32 * epsilon) : k),
      (-(1 / 32 * epsilon) : k), (1 / 8 * epsilon : k)
      ]
      [
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2
    (epsilon : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 16 * epsilon : k), (7 / 32 * epsilon : k), (1 / 4 * epsilon : k),
      (-(1 / 2 * epsilon) : k), (-(1 / 2 * epsilon) : k)
      ]
      [
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd5 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : 2 * B.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree < d)
    (hd8 : C.natDegree + F.natDegree < d)
    (hd9 : D.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : 2 * B.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree < d)
    (hd8 : C.natDegree + F.natDegree < d)
    (hd9 : D.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnEpsilon810 epsilon A B C D E F G = primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1 epsilon A B C D E F G + primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2 epsilon A B C D E F G := by
    simp only [primitiveQuarticColumnEpsilon810, primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1, primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnEpsilon810_live_InfraPrimitivec1_natDegree_lt epsilon A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnEpsilon810_live_InfraPrimitivec2_natDegree_lt epsilon A B C D E F G hd5 hd6 hd7 hd8 hd9)))


theorem primitiveQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroPrimitiveQuartic810` (9 monomials). -/
def primitiveQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

def primitiveQuarticColumnZeta810_live_InfraPrimitivec1
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnZeta810_live_InfraPrimitivec1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnZeta810_live_InfraPrimitivec1
    (zeta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnZeta810_live_InfraPrimitivec1 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8192 * zeta : k), (3 / 512 * zeta : k), (-(3 / 2048 * zeta) : k),
      (3 / 128 * zeta : k), (3 / 32 * zeta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnZeta810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnZeta810_live_InfraPrimitivec1 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnZeta810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnZeta810_live_InfraPrimitivec2
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnZeta810_live_InfraPrimitivec2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnZeta810_live_InfraPrimitivec2
    (zeta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnZeta810_live_InfraPrimitivec2 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k),
      (-(3 / 16 * zeta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnZeta810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (primitiveQuarticColumnZeta810_live_InfraPrimitivec2 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnZeta810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnZeta810 zeta A B C D E F G = primitiveQuarticColumnZeta810_live_InfraPrimitivec1 zeta A B C D E F G + primitiveQuarticColumnZeta810_live_InfraPrimitivec2 zeta A B C D E F G := by
    simp only [primitiveQuarticColumnZeta810, primitiveQuarticColumnZeta810_live_InfraPrimitivec1, primitiveQuarticColumnZeta810_live_InfraPrimitivec2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnZeta810_live_InfraPrimitivec1_natDegree_lt zeta A B C D E F G hd0 hd1 hd2 hd3 hd4) (primitiveQuarticColumnZeta810_live_InfraPrimitivec2_natDegree_lt zeta A B C D E F G hd5 hd6 hd7 hd8)))


theorem primitiveQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroPrimitiveQuartic810` (7 monomials). -/
def primitiveQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 512 * eta : k)) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)

def primitiveQuarticColumnEta810_live_InfraPrimitivec1
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 512 * eta : k)) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEta810_live_InfraPrimitivec1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEta810_live_InfraPrimitivec1
    (eta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEta810_live_InfraPrimitivec1 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 512 * eta) : k), (-(1 / 64 * eta) : k), (1 / 32 * eta : k),
      (3 / 64 * eta : k)
      ]
      [
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEta810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEta810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + B.natDegree < d)
    (hd1 : 2 * A.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd3 : 3 * B.natDegree < d) :
    (primitiveQuarticColumnEta810_live_InfraPrimitivec1 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEta810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnEta810_live_InfraPrimitivec2
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((1 / 4 * eta : k) • (A * F))
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEta810_live_InfraPrimitivec2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEta810_live_InfraPrimitivec2
    (eta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEta810_live_InfraPrimitivec2 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k)
      ]
      [
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEta810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEta810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd4 : A.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnEta810_live_InfraPrimitivec2 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnEta810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + B.natDegree < d)
    (hd1 : 2 * A.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd3 : 3 * B.natDegree < d)
    (hd4 : A.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnEta810 eta A B C D E F G = primitiveQuarticColumnEta810_live_InfraPrimitivec1 eta A B C D E F G + primitiveQuarticColumnEta810_live_InfraPrimitivec2 eta A B C D E F G := by
    simp only [primitiveQuarticColumnEta810, primitiveQuarticColumnEta810_live_InfraPrimitivec1, primitiveQuarticColumnEta810_live_InfraPrimitivec2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnEta810_live_InfraPrimitivec1_natDegree_lt eta A B C D E F G hd0 hd1 hd2 hd3) (primitiveQuarticColumnEta810_live_InfraPrimitivec2_natDegree_lt eta A B C D E F G hd4 hd5 hd6)))


theorem primitiveQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroPrimitiveQuartic810` (7 monomials). -/
def primitiveQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

def primitiveQuarticColumnTheta810_live_InfraPrimitivec1
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnTheta810_live_InfraPrimitivec1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnTheta810_live_InfraPrimitivec1
    (theta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnTheta810_live_InfraPrimitivec1 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 4096 * theta : k), (3 / 128 * theta : k), (1 / 128 * theta : k),
      (1 / 8 * theta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnTheta810_live_InfraPrimitivec1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_live_InfraPrimitivec1_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnTheta810_live_InfraPrimitivec1 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnTheta810_live_InfraPrimitivec1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def primitiveQuarticColumnTheta810_live_InfraPrimitivec2
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((1 / 8 * theta : k) • (B * D))
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnTheta810_live_InfraPrimitivec2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnTheta810_live_InfraPrimitivec2
    (theta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnTheta810_live_InfraPrimitivec2 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k), (1 * theta : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [primitiveQuarticColumnTheta810_live_InfraPrimitivec2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_live_InfraPrimitivec2_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (primitiveQuarticColumnTheta810_live_InfraPrimitivec2 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraPrimitive_primitiveQuarticColumnTheta810_live_InfraPrimitivec2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_natDegree_lt
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
    (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  have hsplit : primitiveQuarticColumnTheta810 theta A B C D E F G = primitiveQuarticColumnTheta810_live_InfraPrimitivec1 theta A B C D E F G + primitiveQuarticColumnTheta810_live_InfraPrimitivec2 theta A B C D E F G := by
    simp only [primitiveQuarticColumnTheta810, primitiveQuarticColumnTheta810_live_InfraPrimitivec1, primitiveQuarticColumnTheta810_live_InfraPrimitivec2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (primitiveQuarticColumnTheta810_live_InfraPrimitivec1_natDegree_lt theta A B C D E F G hd0 hd1 hd2 hd3) (primitiveQuarticColumnTheta810_live_InfraPrimitivec2_natDegree_lt theta A B C D E F G hd4 hd5 hd6)))


theorem primitiveQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    primitiveQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [primitiveQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroPrimitiveQuartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroPrimitiveQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticLoadFree810 A B C D E F G +
      primitiveQuarticColumnL1810 l A B C D E F G +
      primitiveQuarticColumnL2810 l A B C D E F G +
      primitiveQuarticColumnBeta810 beta A B C D E F G +
      primitiveQuarticColumnGamma810 gamma A B C D E F G +
      primitiveQuarticColumnDelta810 delta A B C D E F G +
      primitiveQuarticColumnEpsilon810 epsilon A B C D E F G +
      primitiveQuarticColumnZeta810 zeta A B C D E F G +
      primitiveQuarticColumnEta810 eta A B C D E F G +
      primitiveQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, primitiveQuarticLoadFree810, primitiveQuarticColumnL1810, primitiveQuarticColumnL2810, primitiveQuarticColumnBeta810, primitiveQuarticColumnGamma810, primitiveQuarticColumnDelta810, primitiveQuarticColumnEpsilon810, primitiveQuarticColumnZeta810, primitiveQuarticColumnEta810, primitiveQuarticColumnTheta810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraPrimitive810

end Max11DegreeRoutes
