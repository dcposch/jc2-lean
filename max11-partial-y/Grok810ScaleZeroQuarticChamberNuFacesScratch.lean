import Grok810ScaleZeroQuarticChamberResidual2Scratch
import Max11SpeedReflectDegLibScratch

/-! # `ν` faces and the carrier-change face packets, `(8,10)` scale zero

`…ChamberFacesScratch` emits the load-free/column split for `κ, μ, ξ, π`
only.  The carrier-change kills need the same infrastructure for `ν`
(the two `no_monomial_target` leaves whose saturating set is `{κ, ν}`,
and 4 more), plus 2 further face packets and 22 further load-free
rest bounds for the carriers the change picks — `π` and `ξ` have `γ`/`ε`
columns of letter count ≥ 2, which is what corner `H` needs.
Untracked working note.
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

section QuarticChamberNuFaces810

/-! ## `ν`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroNuQuartic810` (13 monomials). -/
def nuQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroNuQuartic810` (16 monomials). -/
def nuQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

def nuQuarticColumnL810_live_NuFacesc1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnL810_live_NuFacesc1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnL810_live_NuFacesc1
    (l : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnL810_live_NuFacesc1 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (105 / 4194304 * l : k), (135 / 262144 * l : k), (9 / 4096 * l : k),
      (9 / 8192 * l : k), (9 / 16384 * l : k), (63 / 4096 * l : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnL810_live_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_live_NuFacesc1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (nuQuarticColumnL810_live_NuFacesc1 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnL810_live_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def nuQuarticColumnL810_live_NuFacesc2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnL810_live_NuFacesc2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnL810_live_NuFacesc2
    (l : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnL810_live_NuFacesc2 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (315 / 32768 * l : k), (9 / 1024 * l : k), (-(9 / 256 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnL810_live_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_live_NuFacesc2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd6 : 4 * B.natDegree < d)
    (hd7 : 2 * A.natDegree + G.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d) :
    (nuQuarticColumnL810_live_NuFacesc2 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnL810_live_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def nuQuarticColumnL810_live_NuFacesc3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((21 / 1024 * l : k) • C ^ 3)
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnL810_live_NuFacesc3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnL810_live_NuFacesc3
    (l : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnL810_live_NuFacesc3 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(21 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [nuQuarticColumnL810_live_NuFacesc3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_live_NuFacesc3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd12 : 3 * C.natDegree < d)
    (hd13 : C.natDegree + G.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810_live_NuFacesc3 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnL810_live_NuFacesc3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : 2 * A.natDegree + G.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : C.natDegree + G.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  have hsplit : nuQuarticColumnL810 l A B C D E F G = nuQuarticColumnL810_live_NuFacesc1 l A B C D E F G + nuQuarticColumnL810_live_NuFacesc2 l A B C D E F G + nuQuarticColumnL810_live_NuFacesc3 l A B C D E F G := by
    simp only [nuQuarticColumnL810, nuQuarticColumnL810_live_NuFacesc1, nuQuarticColumnL810_live_NuFacesc2, nuQuarticColumnL810_live_NuFacesc3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticColumnL810_live_NuFacesc1_natDegree_lt l A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticColumnL810_live_NuFacesc2_natDegree_lt l A B C D E F G hd6 hd7 hd8 hd9 hd10 hd11))) (nuQuarticColumnL810_live_NuFacesc3_natDegree_lt l A B C D E F G hd12 hd13 hd14 hd15)))


theorem nuQuarticColumnL810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnL810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnL810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroNuQuartic810` (9 monomials). -/
def nuQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

def nuQuarticColumnBeta810_live_NuFacesc1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnBeta810_live_NuFacesc1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnBeta810_live_NuFacesc1
    (beta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnBeta810_live_NuFacesc1 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 65536 * beta : k), (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k),
      (7 / 1024 * beta : k), (7 / 256 * beta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnBeta810_live_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_live_NuFacesc1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d) :
    (nuQuarticColumnBeta810_live_NuFacesc1 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnBeta810_live_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def nuQuarticColumnBeta810_live_NuFacesc2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnBeta810_live_NuFacesc2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnBeta810_live_NuFacesc2
    (beta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnBeta810_live_NuFacesc2 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnBeta810_live_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_live_NuFacesc2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (nuQuarticColumnBeta810_live_NuFacesc2 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnBeta810_live_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
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
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  have hsplit : nuQuarticColumnBeta810 beta A B C D E F G = nuQuarticColumnBeta810_live_NuFacesc1 beta A B C D E F G + nuQuarticColumnBeta810_live_NuFacesc2 beta A B C D E F G := by
    simp only [nuQuarticColumnBeta810, nuQuarticColumnBeta810_live_NuFacesc1, nuQuarticColumnBeta810_live_NuFacesc2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticColumnBeta810_live_NuFacesc1_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4) (nuQuarticColumnBeta810_live_NuFacesc2_natDegree_lt beta A B C D E F G hd5 hd6 hd7 hd8)))


theorem nuQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroNuQuartic810` (5 monomials). -/
def nuQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B * C)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 32 * gamma : k) • (A * F)
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnGamma810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * gamma : k), (5 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k)
      ]
      [
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem nuQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroNuQuartic810` (6 monomials). -/
def nuQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 32768 * delta : k) • A ^ 4
  + (5 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 512 * delta : k) • (A * B ^ 2)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnDelta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 32768 * delta : k), (5 / 1024 * delta : k), (15 / 512 * delta : k),
      (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [nuQuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnDelta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem nuQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroNuQuartic810` (3 monomials). -/
def nuQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 16 * epsilon : k)) • (A * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnEpsilon810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 16 * epsilon) : k), (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k)
      ]
      [
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [nuQuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem nuQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroNuQuartic810` (3 monomials). -/
def nuQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 512 * zeta : k) • A ^ 3
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnZeta810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 512 * zeta : k), (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [nuQuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d)
    (hd2 : E.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem nuQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroNuQuartic810` (2 monomials). -/
def nuQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 32 * eta : k)) • (A * B)
  + (1 / 4 * eta : k) • D

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnEta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 32 * eta) : k), (1 / 4 * eta : k)
      ]
      [
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem nuQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroNuQuartic810` (2 monomials). -/
def nuQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnTheta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 128 * theta : k), (1 / 8 * theta : k)
      ]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem nuQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    nuQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [nuQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroNuQuartic810` into its load-free
part and its eight load columns. -/
theorem degreeZeroNuQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      nuQuarticLoadFree810 A B C D E F G +
      nuQuarticColumnL810 l A B C D E F G +
      nuQuarticColumnBeta810 beta A B C D E F G +
      nuQuarticColumnGamma810 gamma A B C D E F G +
      nuQuarticColumnDelta810 delta A B C D E F G +
      nuQuarticColumnEpsilon810 epsilon A B C D E F G +
      nuQuarticColumnZeta810 zeta A B C D E F G +
      nuQuarticColumnEta810 eta A B C D E F G +
      nuQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroNuQuartic810, nuQuarticLoadFree810, nuQuarticColumnL810, nuQuarticColumnBeta810, nuQuarticColumnGamma810, nuQuarticColumnDelta810, nuQuarticColumnEpsilon810, nuQuarticColumnZeta810, nuQuarticColumnEta810, nuQuarticColumnTheta810]
  module

/-! ## Face / rest splits the carrier change needs -/

set_option maxHeartbeats 64000000 in
/-- Face of `ν` on packet 1000 (1 monomial, top degree `D.natDegree + G.natDegree`). -/
def nuQuarticChamberFace1000810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ν` off packet 1000 (12 monomials). -/
def nuQuarticChamberRestLF1000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticLoadFree810_eq_face1000_add_rest
    (A B C D E F G : k[X]) :
    nuQuarticLoadFree810 A B C D E F G =
      nuQuarticChamberFace1000810 A B C D E F G + nuQuarticChamberRestLF1000810 A B C D E F G := by
  simp only [nuQuarticLoadFree810, nuQuarticChamberFace1000810, nuQuarticChamberRestLF1000810]
  module

set_option maxHeartbeats 64000000 in
/-- Face of `π` on packet 2000 (5 monomial, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace2000810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * F)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 2000 (16 monomials). -/
def piQuarticChamberRestLF2000810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face2000_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace2000810 A B C D E F G + piQuarticChamberRestLF2000810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace2000810, piQuarticChamberRestLF2000810]
  module

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_DF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810` (20 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(5 / 16) : k), (-(15 / 16) : k), (-(5 / 8) : k),
      (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF1000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + 2 * D.natDegree < d) :
    (nuQuarticChamberRestLF1000810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : 2 * C.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1]
      ] := by
  simp only [nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + G.natDegree < d) :
    (nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 128 : k) • (A * C * F))
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k)
      ]
      [
      [1, 0, 1, 0, 0, 1, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0]
      ] := by
  simp only [nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * C.natDegree + D.natDegree < d) :
    (nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * C.natDegree + D.natDegree < d) :
    (nuQuarticChamberRestLF1000810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : nuQuarticChamberRestLF1000810 A B C D 0 F G = nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1 A B C D 0 F G + nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2 A B C D 0 F G := by
    simp only [nuQuarticChamberRestLF1000810, nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1, nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc1_natDegree_lt A B C D 0 F G hdpos hd0 hd1 hd2 hd3 hd4) (nuQuarticChamberRestLF1000810_liveBCDFG_NuFacesc2_natDegree_lt A B C D 0 F G hdpos hd5 hd6 hd7 hd8)))


def nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (-(5 / 128) : k),
      (-(5 / 128) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + E.natDegree < d) :
    (nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 128 : k) • (B ^ 2 * F))
  - (15 / 128 : k) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d)
    (hd6 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d)
    (hd6 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF1000810 A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : nuQuarticChamberRestLF1000810 A B 0 D E F G = nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1 A B 0 D E F G + nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2 A B 0 D E F G := by
    simp only [nuQuarticChamberRestLF1000810, nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1, nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc1_natDegree_lt A B 0 D E F G hdpos hd0 hd1 hd2 hd3) (nuQuarticChamberRestLF1000810_liveBDEFG_NuFacesc2_natDegree_lt A B 0 D E F G hdpos hd4 hd5 hd6)))


def nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (5 / 128 : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (15 / 1024 : k),
      (35 / 512 : k), (-(5 / 128) : k), (-(5 / 128) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 1, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 128 : k) • (A * D * E))
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : B.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * C.natDegree + D.natDegree < d)
    (hd11 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF1000810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : B.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * C.natDegree + D.natDegree < d)
    (hd11 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF1000810 A B C D E F G).natDegree < d := by
  have hsplit : nuQuarticChamberRestLF1000810 A B C D E F G = nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1 A B C D E F G + nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2 A B C D E F G := by
    simp only [nuQuarticChamberRestLF1000810, nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1, nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticChamberRestLF1000810_liveBCDEFG_NuFacesc2_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)))


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF9810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF9810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810` (16 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 32 : k),
      (25 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (45 / 64 : k), (-(15 / 16) : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2000810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF2000810 A B C D 0 F 0 = piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1 A B C D 0 F 0 + piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2 A B C D 0 F 0 := by
    simp only [piQuarticChamberRestLF2000810, piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1, piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF2000810_liveBCDF_NuFacesc1_natDegree_lt A B C D 0 F 0 hdpos hd0 hd1 hd2 hd3) (piQuarticChamberRestLF2000810_liveBCDF_NuFacesc2_natDegree_lt A B C D 0 F 0 hdpos hd4 hd5 hd6)))


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd4 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF2000810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF11810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF11810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF11810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [muQuarticChamberRestLF11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF11810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF4810` (17 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF4810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF4810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 16 : k),
      (5 / 32 : k), (25 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (45 / 64 : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : C.natDegree + 2 * E.natDegree < d)
    (hd11 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : C.natDegree + 2 * E.natDegree < d)
    (hd11 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2000810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF2000810 A B C D E F 0 = piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1 A B C D E F 0 + piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2 A B C D E F 0 := by
    simp only [piQuarticChamberRestLF2000810, piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1, piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF2000810_liveBCDEF_NuFacesc2_natDegree_lt A B C D E F 0 hdpos hd6 hd7 hd8 hd9 hd10 hd11)))


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 32 : k), (25 / 128 : k), (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (-(5 / 8) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (5 / 4 : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : 2 * C.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : 2 * C.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2000810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF2000810 A B C D 0 F G = piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1 A B C D 0 F G + piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2 A B C D 0 F G := by
    simp only [piQuarticChamberRestLF2000810, piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1, piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc1_natDegree_lt A B C D 0 F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF2000810_liveBCDFG_NuFacesc2_natDegree_lt A B C D 0 F G hdpos hd6 hd7 hd8 hd9 hd10)))


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8,
    natDegree_zero, pow_zero, pow_one, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_zero, eq_self_iff_true,
    true_or, or_true, true_and, and_true]
  repeat' apply And.intro
  all_goals exact Or.inr (Or.inr (by omega))

def piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  -((35 / 256 : k) • (B ^ 4 * C))
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 256) : k), (5 / 64 : k), (25 / 128 : k),
      (45 / 64 : k)
      ]
      [
      [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (B * E * F))
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 16) : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d)
    (hd6 : C.natDegree + 2 * E.natDegree < d)
    (hd7 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d)
    (hd6 : C.natDegree + 2 * E.natDegree < d)
    (hd7 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2000810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF2000810 A B C 0 E F G = piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1 A B C 0 E F G + piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2 A B C 0 E F G := by
    simp only [piQuarticChamberRestLF2000810, piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1, piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc1_natDegree_lt A B C 0 E F G hdpos hd0 hd1 hd2 hd3) (piQuarticChamberRestLF2000810_liveBCEFG_NuFacesc2_natDegree_lt A B C 0 E F G hdpos hd4 hd5 hd6 hd7)))


def muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  have hsplit : muQuarticChamberRestLF9810 A B C D E F G = muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1 A B C D E F G + muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2 A B C D E F G := by
    simp only [muQuarticChamberRestLF9810, muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1, muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3) (muQuarticChamberRestLF9810_liveBCDEFG_NuFacesc2_natDegree_lt A B C D E F G hdpos hd4 hd5 hd6)))


def piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (C * D * F))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d)
    (hd15 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberNuFaces_piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2000810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d)
    (hd15 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2000810 A B C D E F G).natDegree < d := by
  have hsplit : piQuarticChamberRestLF2000810 A B C D E F G = piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1 A B C D E F G + piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2 A B C D E F G + piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3 A B C D E F G := by
    simp only [piQuarticChamberRestLF2000810, piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1, piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2, piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc2_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))) (piQuarticChamberRestLF2000810_liveBCDEFG_NuFacesc3_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15)))



end QuarticChamberNuFaces810

end Max11DegreeRoutes
