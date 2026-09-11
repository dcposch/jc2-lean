import Grok810ScaleZeroQuarticDefsScratch

/-! # `ο` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroOmicronQuartic810` has 102 monomials.  `…ChamberFacesPart0Scratch` does this
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

section QuarticChamberInfraOmicron810

/-! ## `ο`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroOmicronQuartic810` (24 monomials). -/
def omicronQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)
  - (5 / 2048 : k) • (A ^ 2 * C * F)
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroOmicronQuartic810`, chunk 1/2 (20 monomials). -/
def omicronQuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)

def omicronQuarticColumnL1810_live_InfraOmicronc1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810_live_InfraOmicronc1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc1
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810_live_InfraOmicronc1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (81 / 262144 * l : k), (-(9 / 65536 * l) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnL1810_live_InfraOmicronc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_live_InfraOmicronc1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d) :
    (omicronQuarticColumnL1810_live_InfraOmicronc1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnL1810_live_InfraOmicronc2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810_live_InfraOmicronc2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc2
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810_live_InfraOmicronc2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (99 / 131072 * l : k), (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k),
      (9 / 8192 * l : k), (-(9 / 4096 * l) : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
      [2, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [omicronQuarticColumnL1810_live_InfraOmicronc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_live_InfraOmicronc2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 3 * A.natDegree + G.natDegree < d)
    (hd9 : 2 * A.natDegree + B.natDegree + F.natDegree < d) :
    (omicronQuarticColumnL1810_live_InfraOmicronc2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnL1810_live_InfraOmicronc3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810_live_InfraOmicronc3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc3
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810_live_InfraOmicronc3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 8192 * l : k), (45 / 4096 * l : k), (99 / 4096 * l : k),
      (9 / 8192 * l : k), (189 / 8192 * l : k)
      ]
      [
      [2, 0, 1, 0, 1, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0],
      [0, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnL1810_live_InfraOmicronc3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_live_InfraOmicronc3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : A.natDegree + 3 * C.natDegree < d)
    (hd14 : 3 * B.natDegree + D.natDegree < d) :
    (omicronQuarticColumnL1810_live_InfraOmicronc3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnL1810_live_InfraOmicronc4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810_live_InfraOmicronc4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc4
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810_live_InfraOmicronc4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (567 / 16384 * l : k), (9 / 512 * l : k), (-(9 / 256 * l) : k),
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k)
      ]
      [
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [omicronQuarticColumnL1810_live_InfraOmicronc4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_live_InfraOmicronc4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd16 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd17 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd18 : 2 * B.natDegree + G.natDegree < d)
    (hd19 : B.natDegree + C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnL1810_live_InfraOmicronc4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL1810_live_InfraOmicronc4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_natDegree_lt
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
    (hd11 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : A.natDegree + 3 * C.natDegree < d)
    (hd14 : 3 * B.natDegree + D.natDegree < d)
    (hd15 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd16 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd17 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd18 : 2 * B.natDegree + G.natDegree < d)
    (hd19 : B.natDegree + C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  have hsplit : omicronQuarticColumnL1810 l A B C D E F G = omicronQuarticColumnL1810_live_InfraOmicronc1 l A B C D E F G + omicronQuarticColumnL1810_live_InfraOmicronc2 l A B C D E F G + omicronQuarticColumnL1810_live_InfraOmicronc3 l A B C D E F G + omicronQuarticColumnL1810_live_InfraOmicronc4 l A B C D E F G := by
    simp only [omicronQuarticColumnL1810, omicronQuarticColumnL1810_live_InfraOmicronc1, omicronQuarticColumnL1810_live_InfraOmicronc2, omicronQuarticColumnL1810_live_InfraOmicronc3, omicronQuarticColumnL1810_live_InfraOmicronc4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (omicronQuarticColumnL1810_live_InfraOmicronc1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (omicronQuarticColumnL1810_live_InfraOmicronc2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (omicronQuarticColumnL1810_live_InfraOmicronc3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (omicronQuarticColumnL1810_live_InfraOmicronc4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem omicronQuarticColumnL1810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroOmicronQuartic810`, chunk 2/2 (5 monomials). -/
def omicronQuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 512 * l : k)) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 512 * l) : k), (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k),
      (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [omicronQuarticColumnL2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * D.natDegree < d)
    (hd3 : E.natDegree + G.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnL2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem omicronQuarticColumnL2810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroOmicronQuartic810` (15 monomials). -/
def omicronQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

def omicronQuarticColumnBeta810_live_InfraOmicronc1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnBeta810_live_InfraOmicronc1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnBeta810_live_InfraOmicronc1
    (beta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810_live_InfraOmicronc1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2097152 * beta : k), (49 / 131072 * beta : k), (-(35 / 131072 * beta) : k),
      (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnBeta810_live_InfraOmicronc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_live_InfraOmicronc1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d) :
    (omicronQuarticColumnBeta810_live_InfraOmicronc1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnBeta810_live_InfraOmicronc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnBeta810_live_InfraOmicronc2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnBeta810_live_InfraOmicronc2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnBeta810_live_InfraOmicronc2
    (beta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810_live_InfraOmicronc2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 8192 * beta : k), (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k)
      ]
      [
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnBeta810_live_InfraOmicronc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_live_InfraOmicronc2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d) :
    (omicronQuarticColumnBeta810_live_InfraOmicronc2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnBeta810_live_InfraOmicronc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnBeta810_live_InfraOmicronc3
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnBeta810_live_InfraOmicronc3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnBeta810_live_InfraOmicronc3
    (beta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810_live_InfraOmicronc3 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 1024 * beta : k), (21 / 256 * beta : k), (7 / 512 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [omicronQuarticColumnBeta810_live_InfraOmicronc3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_live_InfraOmicronc3_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : D.natDegree + F.natDegree < d)
    (hd14 : 2 * E.natDegree < d) :
    (omicronQuarticColumnBeta810_live_InfraOmicronc3 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnBeta810_live_InfraOmicronc3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_natDegree_lt
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
    (hd8 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : D.natDegree + F.natDegree < d)
    (hd14 : 2 * E.natDegree < d) :
    (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  have hsplit : omicronQuarticColumnBeta810 beta A B C D E F G = omicronQuarticColumnBeta810_live_InfraOmicronc1 beta A B C D E F G + omicronQuarticColumnBeta810_live_InfraOmicronc2 beta A B C D E F G + omicronQuarticColumnBeta810_live_InfraOmicronc3 beta A B C D E F G := by
    simp only [omicronQuarticColumnBeta810, omicronQuarticColumnBeta810_live_InfraOmicronc1, omicronQuarticColumnBeta810_live_InfraOmicronc2, omicronQuarticColumnBeta810_live_InfraOmicronc3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (omicronQuarticColumnBeta810_live_InfraOmicronc1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4) (omicronQuarticColumnBeta810_live_InfraOmicronc2_natDegree_lt beta A B C D E F G hd5 hd6 hd7 hd8 hd9))) (omicronQuarticColumnBeta810_live_InfraOmicronc3_natDegree_lt beta A B C D E F G hd10 hd11 hd12 hd13 hd14)))


theorem omicronQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroOmicronQuartic810` (9 monomials). -/
def omicronQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)

def omicronQuarticColumnGamma810_live_InfraOmicronc1
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnGamma810_live_InfraOmicronc1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnGamma810_live_InfraOmicronc1
    (gamma : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnGamma810_live_InfraOmicronc1 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k), (-(3 / 512 * gamma) : k),
      (3 / 128 * gamma : k), (3 / 128 * gamma : k)
      ]
      [
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnGamma810_live_InfraOmicronc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_live_InfraOmicronc1_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d) :
    (omicronQuarticColumnGamma810_live_InfraOmicronc1 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnGamma810_live_InfraOmicronc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnGamma810_live_InfraOmicronc2
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnGamma810_live_InfraOmicronc2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnGamma810_live_InfraOmicronc2
    (gamma : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnGamma810_live_InfraOmicronc2 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [omicronQuarticColumnGamma810_live_InfraOmicronc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_live_InfraOmicronc2_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree < d)
    (hd7 : C.natDegree + F.natDegree < d)
    (hd8 : D.natDegree + E.natDegree < d) :
    (omicronQuarticColumnGamma810_live_InfraOmicronc2 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnGamma810_live_InfraOmicronc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
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
    (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hsplit : omicronQuarticColumnGamma810 gamma A B C D E F G = omicronQuarticColumnGamma810_live_InfraOmicronc1 gamma A B C D E F G + omicronQuarticColumnGamma810_live_InfraOmicronc2 gamma A B C D E F G := by
    simp only [omicronQuarticColumnGamma810, omicronQuarticColumnGamma810_live_InfraOmicronc1, omicronQuarticColumnGamma810_live_InfraOmicronc2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (omicronQuarticColumnGamma810_live_InfraOmicronc1_natDegree_lt gamma A B C D E F G hd0 hd1 hd2 hd3 hd4) (omicronQuarticColumnGamma810_live_InfraOmicronc2_natDegree_lt gamma A B C D E F G hd5 hd6 hd7 hd8)))


theorem omicronQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroOmicronQuartic810` (9 monomials). -/
def omicronQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

def omicronQuarticColumnDelta810_live_InfraOmicronc1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnDelta810_live_InfraOmicronc1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnDelta810_live_InfraOmicronc1
    (delta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnDelta810_live_InfraOmicronc1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 131072 * delta : k), (5 / 4096 * delta : k), (-(5 / 4096 * delta) : k),
      (5 / 128 * delta : k), (5 / 512 * delta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnDelta810_live_InfraOmicronc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_live_InfraOmicronc1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d) :
    (omicronQuarticColumnDelta810_live_InfraOmicronc1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnDelta810_live_InfraOmicronc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def omicronQuarticColumnDelta810_live_InfraOmicronc2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnDelta810_live_InfraOmicronc2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnDelta810_live_InfraOmicronc2
    (delta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnDelta810_live_InfraOmicronc2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 * delta : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 128 * delta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnDelta810_live_InfraOmicronc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_live_InfraOmicronc2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (omicronQuarticColumnDelta810_live_InfraOmicronc2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnDelta810_live_InfraOmicronc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : omicronQuarticColumnDelta810 delta A B C D E F G = omicronQuarticColumnDelta810_live_InfraOmicronc1 delta A B C D E F G + omicronQuarticColumnDelta810_live_InfraOmicronc2 delta A B C D E F G := by
    simp only [omicronQuarticColumnDelta810, omicronQuarticColumnDelta810_live_InfraOmicronc1, omicronQuarticColumnDelta810_live_InfraOmicronc2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (omicronQuarticColumnDelta810_live_InfraOmicronc1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3 hd4) (omicronQuarticColumnDelta810_live_InfraOmicronc2_natDegree_lt delta A B C D E F G hd5 hd6 hd7 hd8)))


theorem omicronQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroOmicronQuartic810` (6 monomials). -/
def omicronQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 256 * epsilon : k)) • (A ^ 2 * D)
  + (1 / 32 * epsilon : k) • (A * B * C)
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 16 * epsilon : k) • (A * F)
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnEpsilon810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 256 * epsilon) : k), (1 / 32 * epsilon : k), (1 / 32 * epsilon : k),
      (-(1 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k)
      ]
      [
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : A.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + D.natDegree < d) :
    (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem omicronQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroOmicronQuartic810` (6 monomials). -/
def omicronQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (9 / 512 * zeta : k) • (A * B ^ 2)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnZeta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 32768 * zeta : k), (3 / 1024 * zeta : k), (9 / 512 * zeta : k),
      (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [omicronQuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem omicronQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroOmicronQuartic810` (4 monomials). -/
def omicronQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 512 * eta : k)) • (A ^ 2 * B)
  - (1 / 32 * eta : k) • (A * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnEta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 512 * eta) : k), (-(1 / 32 * eta) : k), (-(3 / 32 * eta) : k),
      (1 / 4 * eta : k)
      ]
      [
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [omicronQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + B.natDegree < d)
    (hd1 : A.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree < d)
    (hd3 : F.natDegree < d) :
    (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem omicronQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroOmicronQuartic810` (4 monomials). -/
def omicronQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 1024 * theta : k) • A ^ 3
  + (1 / 64 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnTheta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 1024 * theta : k), (1 / 64 * theta : k), (-(3 / 128 * theta) : k),
      (1 / 8 * theta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [omicronQuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraOmicron_omicronQuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem omicronQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    omicronQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [omicronQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroOmicronQuartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroOmicronQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      omicronQuarticLoadFree810 A B C D E F G +
      omicronQuarticColumnL1810 l A B C D E F G +
      omicronQuarticColumnL2810 l A B C D E F G +
      omicronQuarticColumnBeta810 beta A B C D E F G +
      omicronQuarticColumnGamma810 gamma A B C D E F G +
      omicronQuarticColumnDelta810 delta A B C D E F G +
      omicronQuarticColumnEpsilon810 epsilon A B C D E F G +
      omicronQuarticColumnZeta810 zeta A B C D E F G +
      omicronQuarticColumnEta810 eta A B C D E F G +
      omicronQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroOmicronQuartic810, omicronQuarticLoadFree810, omicronQuarticColumnL1810, omicronQuarticColumnL2810, omicronQuarticColumnBeta810, omicronQuarticColumnGamma810, omicronQuarticColumnDelta810, omicronQuarticColumnEpsilon810, omicronQuarticColumnZeta810, omicronQuarticColumnEta810, omicronQuarticColumnTheta810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraOmicron810

end Max11DegreeRoutes
