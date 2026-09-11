import Grok810ScaleZeroQuarticDefsScratch

/-! # Cost-argmin faces and rests, part 0: the carriers, `(8,10)` scale zero

For each carrier `κ, μ, ξ, π`: the load-free part, the eight load
columns (chunked at 20 monomials) with their `natDegree` bounds and
`_zero` lemmas, and the cone-free module identity splitting the integral
into them.  Imported by every other `…FacesPart*` module.  Untracked note.
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

section QuarticChamberFaces810

/-! ## `κ`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroKappaQuartic810` (6 monomials). -/
def kappaQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroKappaQuartic810` (11 monomials). -/
def kappaQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * l : k) • A ^ 5
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnL810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnL810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * l : k), (45 / 8192 * l : k), (-(9 / 16384 * l) : k),
      (27 / 1024 * l : k), (-(9 / 512 * l) : k), (9 / 1024 * l : k),
      (-(63 / 1024 * l) : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [kappaQuarticColumnL810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnL810_natDegree_lt
    {d : ℕ}
    (l : k)
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
    (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnL810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnL810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnL810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnL810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroKappaQuartic810` (7 monomials). -/
def kappaQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnBeta810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnBeta810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k),
      (7 / 64 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (7 / 8 * beta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [kappaQuarticColumnBeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnBeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroKappaQuartic810` (2 monomials). -/
def kappaQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (B * C)
  + (3 / 4 * gamma : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnGamma810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k)
      ]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [kappaQuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroKappaQuartic810` (4 monomials). -/
def kappaQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnDelta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k)
      ]
      [
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [kappaQuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnDelta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroKappaQuartic810` (1 monomials). -/
def kappaQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 2 * epsilon : k) • D

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnEpsilon810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 2 * epsilon : k)
      ]
      [
      [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [kappaQuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : D.natDegree < d) :
    (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroKappaQuartic810` (2 monomials). -/
def kappaQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnZeta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * zeta : k), (3 / 8 * zeta : k)
      ]
      [
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [kappaQuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroKappaQuartic810` (1 monomials). -/
def kappaQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • B

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnEta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)
      ]
      [
      [0, 1, 0, 0, 0, 0, 0]
      ] := by
  simp only [kappaQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree < d) :
    (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroKappaQuartic810` (1 monomials). -/
def kappaQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticColumnTheta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    kappaQuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [1, 0, 0, 0, 0, 0, 0]
      ] := by
  simp only [kappaQuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree < d) :
    (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_kappaQuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem kappaQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    kappaQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [kappaQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroKappaQuartic810` into its load-free part and its eight load columns. -/
theorem degreeZeroKappaQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      kappaQuarticLoadFree810 A B C D E F G +
      kappaQuarticColumnL810 l A B C D E F G +
      kappaQuarticColumnBeta810 beta A B C D E F G +
      kappaQuarticColumnGamma810 gamma A B C D E F G +
      kappaQuarticColumnDelta810 delta A B C D E F G +
      kappaQuarticColumnEpsilon810 epsilon A B C D E F G +
      kappaQuarticColumnZeta810 zeta A B C D E F G +
      kappaQuarticColumnEta810 eta A B C D E F G +
      kappaQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticLoadFree810, kappaQuarticColumnL810, kappaQuarticColumnBeta810, kappaQuarticColumnGamma810, kappaQuarticColumnDelta810, kappaQuarticColumnEpsilon810, kappaQuarticColumnZeta810, kappaQuarticColumnEta810, kappaQuarticColumnTheta810]
  module

/-! ## `μ`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroMuQuartic810` (10 monomials). -/
def muQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroMuQuartic810` (12 monomials). -/
def muQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 262144 * l : k)) • (A ^ 4 * B)
  - (9 / 8192 * l : k) • (A ^ 3 * D)
  - (9 / 8192 * l : k) • (A ^ 2 * B * C)
  + (63 / 8192 * l : k) • (A * B ^ 3)
  - (9 / 1024 * l : k) • (A ^ 2 * F)
  - (9 / 512 * l : k) • (A * B * E)
  - (9 / 512 * l : k) • (A * C * D)
  - (63 / 1024 * l : k) • (B ^ 2 * D)
  - (63 / 1024 * l : k) • (B * C ^ 2)
  + (9 / 64 * l : k) • (B * G)
  + (9 / 64 * l : k) • (C * F)
  + (9 / 64 * l : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnL810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnL810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 262144 * l) : k), (-(9 / 8192 * l) : k), (-(9 / 8192 * l) : k),
      (63 / 8192 * l : k), (-(9 / 1024 * l) : k), (-(9 / 512 * l) : k),
      (-(9 / 512 * l) : k), (-(63 / 1024 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k)
      ]
      [
      [4, 1, 0, 0, 0, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [muQuarticColumnL810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnL810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree + B.natDegree < d)
    (hd1 : 3 * A.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 3 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd7 : 2 * B.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree < d)
    (hd9 : B.natDegree + G.natDegree < d)
    (hd10 : C.natDegree + F.natDegree < d)
    (hd11 : D.natDegree + E.natDegree < d) :
    (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnL810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnL810_zero (A B C D E F G : k[X]) :
    muQuarticColumnL810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnL810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroMuQuartic810` (7 monomials). -/
def muQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 8192 * beta : k)) • (A ^ 3 * B)
  - (7 / 1024 * beta : k) • (A ^ 2 * D)
  + (7 / 512 * beta : k) • (A * B * C)
  + (21 / 1024 * beta : k) • B ^ 3
  - (7 / 64 * beta : k) • (A * F)
  - (7 / 64 * beta : k) • (B * E)
  - (7 / 64 * beta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnBeta810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnBeta810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 8192 * beta) : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (21 / 1024 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k)
      ]
      [
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [muQuarticColumnBeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + B.natDegree < d)
    (hd1 : 2 * A.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd3 : 3 * B.natDegree < d)
    (hd4 : A.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + D.natDegree < d) :
    (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnBeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    muQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroMuQuartic810` (4 monomials). -/
def muQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2
  + (3 / 4 * gamma : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnGamma810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 128 * gamma : k), (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k),
      (3 / 4 * gamma : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [muQuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * B.natDegree < d)
    (hd1 : B.natDegree + D.natDegree < d)
    (hd2 : 2 * C.natDegree < d)
    (hd3 : G.natDegree < d) :
    (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    muQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroMuQuartic810` (4 monomials). -/
def muQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 1024 * delta : k)) • (A ^ 2 * B)
  - (5 / 64 * delta : k) • (A * D)
  - (15 / 64 * delta : k) • (B * C)
  + (5 / 8 * delta : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnDelta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 1024 * delta) : k), (-(5 / 64 * delta) : k), (-(15 / 64 * delta) : k),
      (5 / 8 * delta : k)
      ]
      [
      [2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [muQuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + B.natDegree < d)
    (hd1 : A.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree < d)
    (hd3 : F.natDegree < d) :
    (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnDelta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    muQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroMuQuartic810` (2 monomials). -/
def muQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • B ^ 2
  + (1 / 2 * epsilon : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnEpsilon810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * epsilon) : k), (1 / 2 * epsilon : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [muQuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * B.natDegree < d)
    (hd1 : E.natDegree < d) :
    (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    muQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroMuQuartic810` (2 monomials). -/
def muQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 64 * zeta : k)) • (A * B)
  + (3 / 8 * zeta : k) • D

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnZeta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 64 * zeta) : k), (3 / 8 * zeta : k)
      ]
      [
      [1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [muQuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    muQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroMuQuartic810` (1 monomials). -/
def muQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • C

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnEta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k)
      ]
      [
      [0, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [muQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : C.natDegree < d) :
    (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    muQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroMuQuartic810` (1 monomials). -/
def muQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • B

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticColumnTheta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_muQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [0, 1, 0, 0, 0, 0, 0]
      ] := by
  simp only [muQuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree < d) :
    (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_muQuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem muQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    muQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroMuQuartic810` into its load-free part and its eight load columns. -/
theorem degreeZeroMuQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      muQuarticLoadFree810 A B C D E F G +
      muQuarticColumnL810 l A B C D E F G +
      muQuarticColumnBeta810 beta A B C D E F G +
      muQuarticColumnGamma810 gamma A B C D E F G +
      muQuarticColumnDelta810 delta A B C D E F G +
      muQuarticColumnEpsilon810 epsilon A B C D E F G +
      muQuarticColumnZeta810 zeta A B C D E F G +
      muQuarticColumnEta810 eta A B C D E F G +
      muQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroMuQuartic810, muQuarticLoadFree810, muQuarticColumnL810, muQuarticColumnBeta810, muQuarticColumnGamma810, muQuarticColumnDelta810, muQuarticColumnEpsilon810, muQuarticColumnZeta810, muQuarticColumnEta810, muQuarticColumnTheta810]
  module

/-! ## `ξ`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroXiQuartic810` (13 monomials). -/
def xiQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroXiQuartic810` (17 monomials). -/
def xiQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 262144 * l : k)) • (A ^ 4 * D)
  + (9 / 16384 * l : k) • (A ^ 3 * B * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 3)
  - (9 / 8192 * l : k) • (A ^ 3 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * E)
  - (9 / 8192 * l : k) • (A ^ 2 * C * D)
  + (171 / 8192 * l : k) • (A * B ^ 2 * D)
  + (9 / 1024 * l : k) • (A * B * C ^ 2)
  + (63 / 2048 * l : k) • (B ^ 3 * C)
  - (9 / 512 * l : k) • (A * C * F)
  - (9 / 512 * l : k) • (A * D * E)
  - (45 / 1024 * l : k) • (B ^ 2 * F)
  - (27 / 256 * l : k) • (B * C * E)
  - (27 / 512 * l : k) • (B * D ^ 2)
  - (63 / 1024 * l : k) • (C ^ 2 * D)
  + (9 / 64 * l : k) • (D * G)
  + (9 / 64 * l : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnL810` (17 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnL810
    (l : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnL810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 262144 * l) : k), (9 / 16384 * l : k), (-(9 / 16384 * l) : k),
      (-(9 / 8192 * l) : k), (9 / 4096 * l : k), (-(9 / 8192 * l) : k),
      (171 / 8192 * l : k), (9 / 1024 * l : k), (63 / 2048 * l : k),
      (-(9 / 512 * l) : k), (-(9 / 512 * l) : k), (-(45 / 1024 * l) : k),
      (-(27 / 256 * l) : k), (-(27 / 512 * l) : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k)
      ]
      [
      [4, 0, 0, 1, 0, 0, 0], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0],
      [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0],
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1],
      [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [xiQuarticColumnL810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnL810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree + D.natDegree < d)
    (hd1 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd8 : 3 * B.natDegree + C.natDegree < d)
    (hd9 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd10 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd11 : 2 * B.natDegree + F.natDegree < d)
    (hd12 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd13 : B.natDegree + 2 * D.natDegree < d)
    (hd14 : 2 * C.natDegree + D.natDegree < d)
    (hd15 : D.natDegree + G.natDegree < d)
    (hd16 : E.natDegree + F.natDegree < d) :
    (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnL810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnL810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnL810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnL810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroXiQuartic810` (10 monomials). -/
def xiQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 8192 * beta : k)) • (A ^ 3 * D)
  + (7 / 2048 * beta : k) • (A ^ 2 * B * C)
  - (7 / 1024 * beta : k) • (A * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 2 * F)
  + (7 / 256 * beta : k) • (A * B * E)
  + (7 / 512 * beta : k) • (A * C * D)
  + (49 / 1024 * beta : k) • (B ^ 2 * D)
  + (7 / 128 * beta : k) • (B * C ^ 2)
  - (7 / 64 * beta : k) • (C * F)
  - (7 / 64 * beta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnBeta810` (10 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnBeta810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 8192 * beta) : k), (7 / 2048 * beta : k), (-(7 / 1024 * beta) : k),
      (-(7 / 1024 * beta) : k), (7 / 256 * beta : k), (7 / 512 * beta : k),
      (49 / 1024 * beta : k), (7 / 128 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k)
      ]
      [
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [xiQuarticColumnBeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
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
    (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnBeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroXiQuartic810` (5 monomials). -/
def xiQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * gamma : k) • (A * B * D)
  + (3 / 32 * gamma : k) • (B ^ 2 * C)
  - (3 / 32 * gamma : k) • (B * F)
  - (3 / 16 * gamma : k) • (C * E)
  - (3 / 32 * gamma : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnGamma810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * gamma : k), (3 / 32 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k), (-(3 / 32 * gamma) : k)
      ]
      [
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [xiQuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree < d)
    (hd2 : B.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + E.natDegree < d)
    (hd4 : 2 * D.natDegree < d) :
    (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroXiQuartic810` (6 monomials). -/
def xiQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 1024 * delta : k)) • (A ^ 2 * D)
  + (5 / 128 * delta : k) • (A * B * C)
  + (5 / 128 * delta : k) • B ^ 3
  - (5 / 64 * delta : k) • (A * F)
  - (5 / 32 * delta : k) • (B * E)
  - (15 / 64 * delta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnDelta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 1024 * delta) : k), (5 / 128 * delta : k), (5 / 128 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 64 * delta) : k)
      ]
      [
      [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [xiQuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : A.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + D.natDegree < d) :
    (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnDelta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroXiQuartic810` (4 monomials). -/
def xiQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • (A * B ^ 2)
  - (3 / 16 * epsilon : k) • (B * D)
  - (1 / 8 * epsilon : k) • C ^ 2
  + (1 / 2 * epsilon : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnEpsilon810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 32 * epsilon : k), (-(3 / 16 * epsilon) : k), (-(1 / 8 * epsilon) : k),
      (1 / 2 * epsilon : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * B.natDegree < d)
    (hd1 : B.natDegree + D.natDegree < d)
    (hd2 : 2 * C.natDegree < d)
    (hd3 : G.natDegree < d) :
    (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroXiQuartic810` (3 monomials). -/
def xiQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 64 * zeta : k)) • (A * D)
  - (3 / 16 * zeta : k) • (B * C)
  + (3 / 8 * zeta : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnZeta810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 64 * zeta) : k), (-(3 / 16 * zeta) : k), (3 / 8 * zeta : k)
      ]
      [
      [1, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [xiQuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroXiQuartic810` (2 monomials). -/
def xiQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 16 * eta : k)) • B ^ 2
  + (1 / 4 * eta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnEta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 16 * eta) : k), (1 / 4 * eta : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [xiQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * B.natDegree < d)
    (hd1 : E.natDegree < d) :
    (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroXiQuartic810` (1 monomials). -/
def xiQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • D

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticColumnTheta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_xiQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [0, 0, 0, 1, 0, 0, 0]
      ] := by
  simp only [xiQuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : D.natDegree < d) :
    (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_xiQuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem xiQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroXiQuartic810` into its load-free part and its eight load columns. -/
theorem degreeZeroXiQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      xiQuarticLoadFree810 A B C D E F G +
      xiQuarticColumnL810 l A B C D E F G +
      xiQuarticColumnBeta810 beta A B C D E F G +
      xiQuarticColumnGamma810 gamma A B C D E F G +
      xiQuarticColumnDelta810 delta A B C D E F G +
      xiQuarticColumnEpsilon810 epsilon A B C D E F G +
      xiQuarticColumnZeta810 zeta A B C D E F G +
      xiQuarticColumnEta810 eta A B C D E F G +
      xiQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroXiQuartic810, xiQuarticLoadFree810, xiQuarticColumnL810, xiQuarticColumnBeta810, xiQuarticColumnGamma810, xiQuarticColumnDelta810, xiQuarticColumnEpsilon810, xiQuarticColumnZeta810, xiQuarticColumnEta810, xiQuarticColumnTheta810]
  module

/-! ## `π`: load-free part and the eight load columns -/

set_option maxHeartbeats 64000000 in
/-- The load-free part of `degreeZeroPiQuartic810` (21 monomials). -/
def piQuarticLoadFree810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroPiQuartic810`, chunk 1/2 (20 monomials). -/
def piQuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnL1810` (20 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnL1810
    (l : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnL1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 131072 * l : k), (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k),
      (9 / 4096 * l : k), (9 / 4096 * l : k), (-(27 / 4096 * l) : k),
      (9 / 4096 * l : k), (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k),
      (-(27 / 1024 * l) : k), (9 / 512 * l : k), (63 / 1024 * l : k),
      (9 / 128 * l : k), (27 / 256 * l : k), (9 / 256 * l : k),
      (63 / 512 * l : k), (189 / 512 * l : k), (63 / 512 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k)
      ]
      [
      [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0],
      [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0],
      [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticColumnL1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 4 * A.natDegree + F.natDegree < d)
    (hd3 : 3 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd6 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd7 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd8 : 5 * B.natDegree < d)
    (hd9 : 2 * A.natDegree + C.natDegree + F.natDegree < d)
    (hd10 : 2 * A.natDegree + D.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd13 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd14 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd15 : 3 * B.natDegree + E.natDegree < d)
    (hd16 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd17 : B.natDegree + 3 * C.natDegree < d)
    (hd18 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd19 : B.natDegree + C.natDegree + G.natDegree < d) :
    (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnL1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnL1810_zero (A B C D E F G : k[X]) :
    piQuarticColumnL1810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnL1810]

set_option maxHeartbeats 64000000 in
/-- The `l` column of `degreeZeroPiQuartic810`, chunk 2/2 (6 monomials). -/
def piQuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 64 * l : k)) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnL2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnL2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 64 * l) : k), (-(9 / 32 * l) : k), (-(27 / 128 * l) : k),
      (-(9 / 16 * l) : k), (-(3 / 32 * l) : k), (9 / 8 * l : k)
      ]
      [
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1]
      ] := by
  simp only [piQuarticColumnL2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : B.natDegree + 2 * E.natDegree < d)
    (hd2 : 2 * C.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * D.natDegree < d)
    (hd5 : F.natDegree + G.natDegree < d) :
    (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnL2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnL2810_zero (A B C D E F G : k[X]) :
    piQuarticColumnL2810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnL2810]

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `degreeZeroPiQuartic810` (15 monomials), split 8+7 for `compute_degree`. -/
def piQuarticColumnBeta810a
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)

def piQuarticColumnBeta810b
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((7 / 64 * beta : k) • (A * C * F))
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnBeta810a` (8 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnBeta810a
    (beta : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnBeta810a beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 4096 * beta : k), (7 / 4096 * beta : k), (-(7 / 1024 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (-(21 / 256 * beta) : k),
      (-(7 / 256 * beta) : k), (-(63 / 512 * beta) : k)
      ]
      [
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0]
      ] := by
  simp only [piQuarticColumnBeta810a, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810a_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd7 : 3 * B.natDegree + C.natDegree < d) :
    (piQuarticColumnBeta810a beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnBeta810a]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnBeta810b` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnBeta810b
    (beta : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnBeta810b beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 64 * beta) : k), (7 / 32 * beta : k), (21 / 128 * beta : k),
      (7 / 16 * beta : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (-(7 / 8 * beta) : k)
      ]
      [
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [piQuarticColumnBeta810b, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810b_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hd8 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + F.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + 2 * D.natDegree < d)
    (hd13 : 2 * C.natDegree + D.natDegree < d)
    (hd14 : E.natDegree + F.natDegree < d) :
    (piQuarticColumnBeta810b beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnBeta810b]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

def piQuarticColumnBeta810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)

theorem piQuarticColumnBeta810_split (beta : k) (A B C D E F G : k[X]) :
    piQuarticColumnBeta810 beta A B C D E F G =
      piQuarticColumnBeta810a beta A B C D E F G + piQuarticColumnBeta810b beta A B C D E F G := by
  simp only [piQuarticColumnBeta810, piQuarticColumnBeta810a, piQuarticColumnBeta810b]
  abel

theorem piQuarticColumnBeta810_natDegree_lt
    {d : ℕ}
    (beta : k)
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
    (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [piQuarticColumnBeta810_split]
  exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
    (max_lt (piQuarticColumnBeta810a_natDegree_lt beta A B C D E F G hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7)
      (piQuarticColumnBeta810b_natDegree_lt beta A B C D E F G hd8 hd9 hd10 hd11 hd12 hd13 hd14))

theorem piQuarticColumnBeta810_zero (A B C D E F G : k[X]) :
    piQuarticColumnBeta810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnBeta810]

set_option maxHeartbeats 64000000 in
/-- The `gamma` column of `degreeZeroPiQuartic810` (8 monomials). -/
def piQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 32 * gamma : k)) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnGamma810` (8 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 32 * gamma) : k), (-(15 / 256 * gamma) : k), (3 / 16 * gamma : k),
      (3 / 8 * gamma : k), (3 / 4 * gamma : k), (1 / 8 * gamma : k),
      (-(3 / 4 * gamma) : k), (-(3 / 4 * gamma) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [piQuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnGamma810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnGamma810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnGamma810_zero (A B C D E F G : k[X]) :
    piQuarticColumnGamma810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnGamma810]

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `degreeZeroPiQuartic810` (9 monomials). -/
def piQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnDelta810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 * delta : k), (-(15 / 256 * delta) : k), (-(5 / 128 * delta) : k),
      (5 / 32 * delta : k), (5 / 32 * delta : k), (15 / 32 * delta : k),
      (15 / 32 * delta : k), (-(5 / 8 * delta) : k), (-(5 / 4 * delta) : k)
      ]
      [
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [piQuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnDelta810_natDegree_lt
    {d : ℕ}
    (delta : k)
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
    (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnDelta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnDelta810_zero (A B C D E F G : k[X]) :
    piQuarticColumnDelta810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnDelta810]

set_option maxHeartbeats 64000000 in
/-- The `epsilon` column of `degreeZeroPiQuartic810` (5 monomials). -/
def piQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnEpsilon810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * epsilon : k), (1 / 2 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k)
      ]
      [
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEpsilon810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree < d)
    (hd2 : B.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + E.natDegree < d)
    (hd4 : 2 * D.natDegree < d) :
    (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnEpsilon810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnEpsilon810_zero (A B C D E F G : k[X]) :
    piQuarticColumnEpsilon810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnEpsilon810]

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `degreeZeroPiQuartic810` (5 monomials). -/
def piQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnZeta810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32 * zeta : k), (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k),
      (-(3 / 4 * zeta) : k), (-(3 / 4 * zeta) : k)
      ]
      [
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnZeta810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnZeta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnZeta810_zero (A B C D E F G : k[X]) :
    piQuarticColumnZeta810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnZeta810]

set_option maxHeartbeats 64000000 in
/-- The `eta` column of `degreeZeroPiQuartic810` (4 monomials). -/
def piQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnEta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 16 * eta : k), (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k),
      (2 * eta : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEta810_natDegree_lt
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * B.natDegree < d)
    (hd1 : B.natDegree + D.natDegree < d)
    (hd2 : 2 * C.natDegree < d)
    (hd3 : G.natDegree < d) :
    (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnEta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnEta810_zero (A B C D E F G : k[X]) :
    piQuarticColumnEta810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnEta810]

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `degreeZeroPiQuartic810` (2 monomials). -/
def piQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 4 * theta : k)) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticColumnTheta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart0_piQuarticColumnTheta810
    (theta : k)
    (A B C D E F G : k[X]) :
    piQuarticColumnTheta810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 4 * theta) : k), (1 * theta : k)
      ]
      [
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticColumnTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticColumnTheta810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart0_piQuarticColumnTheta810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

theorem piQuarticColumnTheta810_zero (A B C D E F G : k[X]) :
    piQuarticColumnTheta810 0 A B C D E F G = 0 := by
  simp [piQuarticColumnTheta810]

set_option maxHeartbeats 64000000 in
/-- Cone-free split of `degreeZeroPiQuartic810` into its load-free part and its eight load columns. -/
theorem degreeZeroPiQuartic810_eq_chamberSplit
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G =
      piQuarticLoadFree810 A B C D E F G +
      piQuarticColumnL1810 l A B C D E F G +
      piQuarticColumnL2810 l A B C D E F G +
      piQuarticColumnBeta810 beta A B C D E F G +
      piQuarticColumnGamma810 gamma A B C D E F G +
      piQuarticColumnDelta810 delta A B C D E F G +
      piQuarticColumnEpsilon810 epsilon A B C D E F G +
      piQuarticColumnZeta810 zeta A B C D E F G +
      piQuarticColumnEta810 eta A B C D E F G +
      piQuarticColumnTheta810 theta A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piQuarticLoadFree810, piQuarticColumnL1810, piQuarticColumnL2810, piQuarticColumnBeta810, piQuarticColumnGamma810, piQuarticColumnDelta810, piQuarticColumnEpsilon810, piQuarticColumnZeta810, piQuarticColumnEta810, piQuarticColumnTheta810, piBaseGroupQuartic810, piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810, piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810, piThetaGroupQuartic810]
  module


end QuarticChamberFaces810

end Max11DegreeRoutes
