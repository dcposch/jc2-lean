import Grok810ScaleZeroQuarticChamberN7LadderScratch
import Max11SpeedReflectDegLibScratch

/-! # `N₃` load-free part, load columns and split, `(8,10)` scale zero

`degreeZeroN3Quartic810` has 97 monomials.  `…ChamberFacesPart0Scratch` does this
for `κ, μ, ξ, π` only; `UNOWNED_CHAMBERS.md` needs the same for `ο`, `Π`
and the auxiliaries `N₂…N₇`, and defines `N₃` itself.  Independent of the sibling
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

section QuarticChamberInfraN3810

set_option maxHeartbeats 64000000 in
/-- `N₃ = ο − (1/16)·A·ν` (weight 15, `natDegree ≤ 1·a`);
the auxiliary `UNOWNED_CHAMBERS.md` adds to the tower. -/
def degreeZeroN3Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (-(1 / 16) : k) • (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN3Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    (degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
      A.natDegree := by
  have hb0 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ A.natDegree := by
    rw [homi]
    omega
  have hb1 : ((-(1 / 16) : k) • (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        A.natDegree + (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [hnu, add_zero] at hmul
    omega
  simp only [degreeZeroN3Quartic810]
  exact natDegree_add_le810 hb0 hb1

/-! ## `N₃`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroN3Quartic810` (19 monomials). -/
def n3QuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (175 / 8192 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (45 / 1024 : k) • (A * B * C * E)
  + (85 / 2048 : k) • (A * B * D ^ 2)
  + (45 / 2048 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 256 : k) • (A * D * G)
  - (15 / 256 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN3Quartic810`, chunk 1/2 (20 monomials). -/
def n3QuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (165 / 67108864 * l : k) • A ^ 7
  + (315 / 4194304 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (45 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 131072 * l : k) • (A ^ 3 * B * D)
  + (189 / 262144 * l : k) • (A ^ 3 * C ^ 2)
  - (171 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (1827 / 524288 * l : k) • (A * B ^ 4)
  + (9 / 16384 * l : k) • (A ^ 3 * G)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (9 / 8192 * l : k) • (A ^ 2 * D ^ 2)
  + (243 / 16384 * l : k) • (A * B ^ 2 * E)
  + (261 / 8192 * l : k) • (A * B * C * D)
  + (39 / 16384 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 1024 * l : k) • (A * C * G)
  - (45 / 1024 * l : k) • (A * D * F)
  - (9 / 2048 * l : k) • (A * E ^ 2)
  - (27 / 1024 * l : k) • (B ^ 2 * G)

def n3QuarticColumnL1810_live_InfraN3c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (165 / 67108864 * l : k) • A ^ 7
  + (315 / 4194304 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (45 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 131072 * l : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810_live_InfraN3c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c1
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810_live_InfraN3c1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (165 / 67108864 * l : k), (315 / 4194304 * l : k), (-(171 / 4194304 * l) : k),
      (45 / 262144 * l : k), (-(27 / 131072 * l) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnL1810_live_InfraN3c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_live_InfraN3c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n3QuarticColumnL1810_live_InfraN3c1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnL1810_live_InfraN3c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (189 / 262144 * l : k) • (A ^ 3 * C ^ 2)
  - (171 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (1827 / 524288 * l : k) • (A * B ^ 4)
  + (9 / 16384 * l : k) • (A ^ 3 * G)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810_live_InfraN3c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c2
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810_live_InfraN3c2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (189 / 262144 * l : k), (-(171 / 131072 * l) : k), (-(1827 / 524288 * l) : k),
      (9 / 16384 * l : k), (27 / 8192 * l : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1],
      [2, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnL1810_live_InfraN3c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_live_InfraN3c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + 4 * B.natDegree < d)
    (hd8 : 3 * A.natDegree + G.natDegree < d)
    (hd9 : 2 * A.natDegree + C.natDegree + E.natDegree < d) :
    (n3QuarticColumnL1810_live_InfraN3c2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnL1810_live_InfraN3c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 8192 * l : k) • (A ^ 2 * D ^ 2)
  + (243 / 16384 * l : k) • (A * B ^ 2 * E)
  + (261 / 8192 * l : k) • (A * B * C * D)
  + (39 / 16384 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810_live_InfraN3c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c3
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810_live_InfraN3c3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 8192 * l : k), (243 / 16384 * l : k), (261 / 8192 * l : k),
      (39 / 16384 * l : k), (189 / 8192 * l : k)
      ]
      [
      [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0],
      [0, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnL1810_live_InfraN3c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_live_InfraN3c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd11 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : A.natDegree + 3 * C.natDegree < d)
    (hd14 : 3 * B.natDegree + D.natDegree < d) :
    (n3QuarticColumnL1810_live_InfraN3c3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnL1810_live_InfraN3c4
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 1024 * l : k) • (A * C * G)
  - (45 / 1024 * l : k) • (A * D * F)
  - (9 / 2048 * l : k) • (A * E ^ 2)
  - (27 / 1024 * l : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810_live_InfraN3c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c4
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810_live_InfraN3c4 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (567 / 16384 * l : k), (9 / 1024 * l : k), (-(45 / 1024 * l) : k),
      (-(9 / 2048 * l) : k), (-(27 / 1024 * l) : k)
      ]
      [
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 2, 0, 0],
      [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [n3QuarticColumnL1810_live_InfraN3c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_live_InfraN3c4_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd15 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd16 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd17 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd18 : A.natDegree + 2 * E.natDegree < d)
    (hd19 : 2 * B.natDegree + G.natDegree < d) :
    (n3QuarticColumnL1810_live_InfraN3c4 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnL1810_live_InfraN3c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_natDegree_lt
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
    (hd9 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd11 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : A.natDegree + 3 * C.natDegree < d)
    (hd14 : 3 * B.natDegree + D.natDegree < d)
    (hd15 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd16 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd17 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd18 : A.natDegree + 2 * E.natDegree < d)
    (hd19 : 2 * B.natDegree + G.natDegree < d) :
    (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  have hsplit : n3QuarticColumnL1810 l A B C D E F G = n3QuarticColumnL1810_live_InfraN3c1 l A B C D E F G + n3QuarticColumnL1810_live_InfraN3c2 l A B C D E F G + n3QuarticColumnL1810_live_InfraN3c3 l A B C D E F G + n3QuarticColumnL1810_live_InfraN3c4 l A B C D E F G := by
    simp only [n3QuarticColumnL1810, n3QuarticColumnL1810_live_InfraN3c1, n3QuarticColumnL1810_live_InfraN3c2, n3QuarticColumnL1810_live_InfraN3c3, n3QuarticColumnL1810_live_InfraN3c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n3QuarticColumnL1810_live_InfraN3c1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4) (n3QuarticColumnL1810_live_InfraN3c2_natDegree_lt l A B C D E F G hd5 hd6 hd7 hd8 hd9))) (n3QuarticColumnL1810_live_InfraN3c3_natDegree_lt l A B C D E F G hd10 hd11 hd12 hd13 hd14))) (n3QuarticColumnL1810_live_InfraN3c4_natDegree_lt l A B C D E F G hd15 hd16 hd17 hd18 hd19)))


theorem n3QuarticColumnL1810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroN3Quartic810`, chunk 2/2 (6 monomials). -/
def n3QuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 128 * l : k)) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * l) : k), (-(45 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 512 * l) : k), (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n3QuarticColumnL2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 2 * C.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + 2 * D.natDegree < d)
    (hd4 : E.natDegree + G.natDegree < d)
    (hd5 : 2 * F.natDegree < d) :
    (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnL2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n3QuarticColumnL2810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroN3Quartic810` (16 monomials). -/
def n3QuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2097152 * beta : k) • A ^ 6
  + (35 / 131072 * beta : k) • (A ^ 4 * C)
  - (63 / 262144 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 16384 * beta : k) • (A ^ 3 * E)
  - (7 / 2048 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (245 / 16384 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 1024 * beta : k) • (A * B * F)
  + (21 / 1024 * beta : k) • (A * C * E)
  + (35 / 2048 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

def n3QuarticColumnBeta810_live_InfraN3c1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2097152 * beta : k) • A ^ 6
  + (35 / 131072 * beta : k) • (A ^ 4 * C)
  - (63 / 262144 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 16384 * beta : k) • (A ^ 3 * E)
  - (7 / 2048 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810_live_InfraN3c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnBeta810_live_InfraN3c1
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810_live_InfraN3c1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 2097152 * beta : k), (35 / 131072 * beta : k), (-(63 / 262144 * beta) : k),
      (7 / 16384 * beta : k), (-(7 / 2048 * beta) : k), (21 / 8192 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810_live_InfraN3c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_live_InfraN3c1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n3QuarticColumnBeta810_live_InfraN3c1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnBeta810_live_InfraN3c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnBeta810_live_InfraN3c2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((245 / 16384 * beta : k) • (A * B ^ 2 * C))
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 1024 * beta : k) • (A * B * F)
  + (21 / 1024 * beta : k) • (A * C * E)
  + (35 / 2048 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810_live_InfraN3c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnBeta810_live_InfraN3c2
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810_live_InfraN3c2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(245 / 16384 * beta) : k), (-(189 / 32768 * beta) : k), (7 / 1024 * beta : k),
      (21 / 1024 * beta : k), (35 / 2048 * beta : k), (35 / 1024 * beta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810_live_InfraN3c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_live_InfraN3c2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d) :
    (n3QuarticColumnBeta810_live_InfraN3c2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnBeta810_live_InfraN3c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnBeta810_live_InfraN3c3
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810_live_InfraN3c3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnBeta810_live_InfraN3c3
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810_live_InfraN3c3 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810_live_InfraN3c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_live_InfraN3c3_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n3QuarticColumnBeta810_live_InfraN3c3 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnBeta810_live_InfraN3c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_natDegree_lt
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
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  have hsplit : n3QuarticColumnBeta810 beta A B C D E F G = n3QuarticColumnBeta810_live_InfraN3c1 beta A B C D E F G + n3QuarticColumnBeta810_live_InfraN3c2 beta A B C D E F G + n3QuarticColumnBeta810_live_InfraN3c3 beta A B C D E F G := by
    simp only [n3QuarticColumnBeta810, n3QuarticColumnBeta810_live_InfraN3c1, n3QuarticColumnBeta810_live_InfraN3c2, n3QuarticColumnBeta810_live_InfraN3c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n3QuarticColumnBeta810_live_InfraN3c1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnBeta810_live_InfraN3c2_natDegree_lt beta A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (n3QuarticColumnBeta810_live_InfraN3c3_natDegree_lt beta A B C D E F G hd12 hd13 hd14 hd15)))


theorem n3QuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroN3Quartic810` (7 monomials). -/
def n3QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(23 / 2048 * gamma : k)) • (A * B ^ 3)
  + (9 / 256 * gamma : k) • (A * B * E)
  + (9 / 256 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)

def n3QuarticColumnGamma810_live_InfraN3c1
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(23 / 2048 * gamma : k)) • (A * B ^ 3)
  + (9 / 256 * gamma : k) • (A * B * E)
  + (9 / 256 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnGamma810_live_InfraN3c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnGamma810_live_InfraN3c1
    (gamma : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnGamma810_live_InfraN3c1 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(23 / 2048 * gamma) : k), (9 / 256 * gamma : k), (9 / 256 * gamma : k),
      (9 / 128 * gamma : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnGamma810_live_InfraN3c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnGamma810_live_InfraN3c1_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + D.natDegree < d) :
    (n3QuarticColumnGamma810_live_InfraN3c1 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnGamma810_live_InfraN3c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnGamma810_live_InfraN3c2
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnGamma810_live_InfraN3c2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnGamma810_live_InfraN3c2
    (gamma : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnGamma810_live_InfraN3c2 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k)
      ]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnGamma810_live_InfraN3c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnGamma810_live_InfraN3c2_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + 2 * C.natDegree < d)
    (hd5 : C.natDegree + F.natDegree < d)
    (hd6 : D.natDegree + E.natDegree < d) :
    (n3QuarticColumnGamma810_live_InfraN3c2 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnGamma810_live_InfraN3c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree < d)
    (hd5 : C.natDegree + F.natDegree < d)
    (hd6 : D.natDegree + E.natDegree < d) :
    (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hsplit : n3QuarticColumnGamma810 gamma A B C D E F G = n3QuarticColumnGamma810_live_InfraN3c1 gamma A B C D E F G + n3QuarticColumnGamma810_live_InfraN3c2 gamma A B C D E F G := by
    simp only [n3QuarticColumnGamma810, n3QuarticColumnGamma810_live_InfraN3c1, n3QuarticColumnGamma810_live_InfraN3c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n3QuarticColumnGamma810_live_InfraN3c1_natDegree_lt gamma A B C D E F G hd0 hd1 hd2 hd3) (n3QuarticColumnGamma810_live_InfraN3c2_natDegree_lt gamma A B C D E F G hd4 hd5 hd6)))


theorem n3QuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroN3Quartic810` (10 monomials). -/
def n3QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 5
  + (15 / 16384 * delta : k) • (A ^ 3 * C)
  - (25 / 8192 * delta : k) • (A ^ 2 * B ^ 2)
  + (55 / 1024 * delta : k) • (A * B * D)
  + (35 / 2048 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 128 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

def n3QuarticColumnDelta810_live_InfraN3c1
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 5
  + (15 / 16384 * delta : k) • (A ^ 3 * C)
  - (25 / 8192 * delta : k) • (A ^ 2 * B ^ 2)
  + (55 / 1024 * delta : k) • (A * B * D)
  + (35 / 2048 * delta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnDelta810_live_InfraN3c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnDelta810_live_InfraN3c1
    (delta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnDelta810_live_InfraN3c1 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 524288 * delta : k), (15 / 16384 * delta : k), (-(25 / 8192 * delta) : k),
      (55 / 1024 * delta : k), (35 / 2048 * delta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnDelta810_live_InfraN3c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_live_InfraN3c1_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d) :
    (n3QuarticColumnDelta810_live_InfraN3c1 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnDelta810_live_InfraN3c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnDelta810_live_InfraN3c2
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * delta : k) • (B ^ 2 * C)
  - (5 / 128 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnDelta810_live_InfraN3c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnDelta810_live_InfraN3c2
    (delta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnDelta810_live_InfraN3c2 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 * delta : k), (-(5 / 128 * delta) : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnDelta810_live_InfraN3c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_live_InfraN3c2_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + E.natDegree < d)
    (hd9 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810_live_InfraN3c2 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnDelta810_live_InfraN3c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + E.natDegree < d)
    (hd9 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  have hsplit : n3QuarticColumnDelta810 delta A B C D E F G = n3QuarticColumnDelta810_live_InfraN3c1 delta A B C D E F G + n3QuarticColumnDelta810_live_InfraN3c2 delta A B C D E F G := by
    simp only [n3QuarticColumnDelta810, n3QuarticColumnDelta810_live_InfraN3c1, n3QuarticColumnDelta810_live_InfraN3c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n3QuarticColumnDelta810_live_InfraN3c1_natDegree_lt delta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n3QuarticColumnDelta810_live_InfraN3c2_natDegree_lt delta A B C D E F G hd5 hd6 hd7 hd8 hd9)))


theorem n3QuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroN3Quartic810` (5 monomials). -/
def n3QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * epsilon : k) • (A * B * C)
  + (1 / 32 * epsilon : k) • B ^ 3
  - (3 / 32 * epsilon : k) • (A * F)
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnEpsilon810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * epsilon : k), (1 / 32 * epsilon : k), (-(3 / 32 * epsilon) : k),
      (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k)
      ]
      [
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n3QuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroN3Quartic810` (7 monomials). -/
def n3QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (51 / 2048 * zeta : k) • (A * B ^ 2)
  - (3 / 128 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G

def n3QuarticColumnZeta810_live_InfraN3c1
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (51 / 2048 * zeta : k) • (A * B ^ 2)
  - (3 / 128 * zeta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnZeta810_live_InfraN3c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnZeta810_live_InfraN3c1
    (zeta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnZeta810_live_InfraN3c1 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32768 * zeta : k), (3 / 1024 * zeta : k), (51 / 2048 * zeta : k),
      (-(3 / 128 * zeta) : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnZeta810_live_InfraN3c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_live_InfraN3c1_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d) :
    (n3QuarticColumnZeta810_live_InfraN3c1 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnZeta810_live_InfraN3c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def n3QuarticColumnZeta810_live_InfraN3c2
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 64 * zeta : k) • (B * D))
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnZeta810_live_InfraN3c2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnZeta810_live_InfraN3c2
    (zeta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnZeta810_live_InfraN3c2 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n3QuarticColumnZeta810_live_InfraN3c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_live_InfraN3c2_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n3QuarticColumnZeta810_live_InfraN3c2 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnZeta810_live_InfraN3c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_natDegree_lt
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
    (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  have hsplit : n3QuarticColumnZeta810 zeta A B C D E F G = n3QuarticColumnZeta810_live_InfraN3c1 zeta A B C D E F G + n3QuarticColumnZeta810_live_InfraN3c2 zeta A B C D E F G := by
    simp only [n3QuarticColumnZeta810, n3QuarticColumnZeta810_live_InfraN3c1, n3QuarticColumnZeta810_live_InfraN3c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (n3QuarticColumnZeta810_live_InfraN3c1_natDegree_lt zeta A B C D E F G hd0 hd1 hd2 hd3) (n3QuarticColumnZeta810_live_InfraN3c2_natDegree_lt zeta A B C D E F G hd4 hd5 hd6)))


theorem n3QuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroN3Quartic810` (3 monomials). -/
def n3QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 64 * eta : k)) • (A * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnEta810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 64 * eta) : k), (-(3 / 32 * eta) : k), (1 / 4 * eta : k)
      ]
      [
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [n3QuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n3QuarticColumnEta810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroN3Quartic810` (4 monomials). -/
def n3QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 2048 * theta : k) • A ^ 3
  + (1 / 128 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnTheta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberInfraN3_n3QuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 2048 * theta : k), (1 / 128 * theta : k), (-(3 / 128 * theta) : k),
      (1 / 8 * theta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberInfraN3_n3QuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem n3QuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroN3Quartic810` into its load-free part and its
eight load columns. -/
theorem degreeZeroN3Quartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN3Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticLoadFree810 A B C D E F G +
      n3QuarticColumnL1810 l A B C D E F G +
      n3QuarticColumnL2810 l A B C D E F G +
      n3QuarticColumnBeta810 beta A B C D E F G +
      n3QuarticColumnGamma810 gamma A B C D E F G +
      n3QuarticColumnDelta810 delta A B C D E F G +
      n3QuarticColumnEpsilon810 epsilon A B C D E F G +
      n3QuarticColumnZeta810 zeta A B C D E F G +
      n3QuarticColumnEta810 eta A B C D E F G +
      n3QuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroN3Quartic810, n3QuarticLoadFree810, n3QuarticColumnL1810, n3QuarticColumnL2810, n3QuarticColumnBeta810, n3QuarticColumnGamma810, n3QuarticColumnDelta810, n3QuarticColumnEpsilon810, n3QuarticColumnZeta810, n3QuarticColumnEta810, n3QuarticColumnTheta810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring


end QuarticChamberInfraN3810

end Max11DegreeRoutes
