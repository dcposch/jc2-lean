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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    by simpa only [Nat.add_assoc] using hd15,
    by simpa only [Nat.add_assoc] using hd16,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    by simpa only [Nat.add_assoc] using hd15,
    by simpa only [Nat.add_assoc] using hd16,
    by simpa only [Nat.add_assoc] using hd17,
    by simpa only [Nat.add_assoc] using hd18,
    by simpa only [Nat.add_assoc] using hd19,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd8⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

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
/-! # Cost-argmin faces and rests, part 1: the packets, `(8,10)` scale zero

The 79 face packets — a packet is a *(carrier, face monomial
set)* pair, since the face depends on the live set as well as on the
argmin — each with its face, its load-free rest and the cone-free packet
split identity.  Definitions and identities only; the rest *bounds* are
in the sibling `…FacesPart2..PartN` modules, which are mutually
independent.  Untracked working note.
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

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BBB, BF·DD, BF·DD·BBB, BF·EE·BBB` (1 monomial, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 0 (5 monomials). -/
def kappaQuarticChamberRestLF0810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace0810 A B C D E F G + kappaQuarticChamberRestLF0810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace0810, kappaQuarticChamberRestLF0810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CCC, CF·CCC` (1 monomial, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 0 (9 monomials). -/
def muQuarticChamberRestLF0810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace0810 A B C D E F G + muQuarticChamberRestLF0810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace0810, muQuarticChamberRestLF0810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·DD, BG·DD·BBB, BG·DD·DG·GG, CF·DD` (1 monomial, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 1 (9 monomials). -/
def muQuarticChamberRestLF1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace1810 A B C D E F G + muQuarticChamberRestLF1810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace1810, muQuarticChamberRestLF1810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·EE, BG·EE·BBB, BG·EE·EG·GG, CF·EE` (1 monomial, top degree `2 * E.natDegree`). -/
def muQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 2 (9 monomials). -/
def muQuarticChamberRestLF2810
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

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace2810 A B C D E F G + muQuarticChamberRestLF2810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace2810, muQuarticChamberRestLF2810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG, BF·BG·CF·CG·FF·FG·GG, BF·CF·EE·EF·FF, BF·EE·EF·FF` (1 monomial, top degree `2 * F.natDegree`). -/
def xiQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 0 (12 monomials). -/
def xiQuarticChamberRestLF0810
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

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace0810 A B C D E F G + xiQuarticChamberRestLF0810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace0810, xiQuarticChamberRestLF0810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·CG·DD·DG·GG, BG·GG, CG·DD, CG·DD·DG·GG` (1 monomial, top degree `2 * G.natDegree`). -/
def piQuarticChamberFace0810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 0 (20 monomials). -/
def piQuarticChamberRestLF0810
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

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face0_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace0810 A B C D E F G + piQuarticChamberRestLF0810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace0810, piQuarticChamberRestLF0810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BBB·BBC·BCC·CCC, EE·BBB·BBC·BCC·CCC` (2 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 1 (4 monomials). -/
def kappaQuarticChamberRestLF1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace1810 A B C D E F G + kappaQuarticChamberRestLF1810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace1810, kappaQuarticChamberRestLF1810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BBB·BBC·BCC·CCC` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 3 (8 monomials). -/
def muQuarticChamberRestLF3810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace3810 A B C D E F G + muQuarticChamberRestLF3810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace3810, muQuarticChamberRestLF3810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF, BF·BBB, BF·BG, BF·BG·BBB` (1 monomial, top degree `A.natDegree + B.natDegree + F.natDegree`). -/
def muQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 4 (9 monomials). -/
def muQuarticChamberRestLF4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace4810 A B C D E F G + muQuarticChamberRestLF4810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace4810, muQuarticChamberRestLF4810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·DD, BF·BG·EE, BG, BG·CG·DD` (1 monomial, top degree `B.natDegree + G.natDegree`). -/
def kappaQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 2 (5 monomials). -/
def kappaQuarticChamberRestLF2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace2810 A B C D E F G + kappaQuarticChamberRestLF2810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace2810, kappaQuarticChamberRestLF2810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·BBB` (1 monomial, top degree `4 * B.natDegree`). -/
def muQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 5 (9 monomials). -/
def muQuarticChamberRestLF5810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace5810 A B C D E F G + muQuarticChamberRestLF5810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace5810, muQuarticChamberRestLF5810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·CCC, CG·DD, CG·DD·CCC, DD·CCC` (1 monomial, top degree `C.natDegree + 2 * D.natDegree`). -/
def xiQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 1 (12 monomials). -/
def xiQuarticChamberRestLF1810
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
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace1810 A B C D E F G + xiQuarticChamberRestLF1810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace1810, xiQuarticChamberRestLF1810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `EE·CCC` (1 monomial, top degree `2 * C.natDegree + E.natDegree`). -/
def xiQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 2 (12 monomials). -/
def xiQuarticChamberRestLF2810
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
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace2810 A B C D E F G + xiQuarticChamberRestLF2810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace2810, xiQuarticChamberRestLF2810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·CF·DD, BF·CF·EE, CF, CF·CG·CCC` (1 monomial, top degree `C.natDegree + F.natDegree`). -/
def kappaQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 3 (5 monomials). -/
def kappaQuarticChamberRestLF3810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace3810 A B C D E F G + kappaQuarticChamberRestLF3810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace3810, kappaQuarticChamberRestLF3810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·CG, BG·CG·GG, CF·CG, CF·CG·FF·FG·GG` (1 monomial, top degree `C.natDegree + G.natDegree`). -/
def muQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 6 (9 monomials). -/
def muQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace6810 A B C D E F G + muQuarticChamberRestLF6810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace6810, muQuarticChamberRestLF6810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CG·CCC` (2 monomials, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 7 (8 monomials). -/
def muQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace7810 A B C D E F G + muQuarticChamberRestLF7810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace7810, muQuarticChamberRestLF7810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CG·CCC` (3 monomials, top degree `4 * C.natDegree`). -/
def piQuarticChamberFace1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 1 (18 monomials). -/
def piQuarticChamberRestLF1810
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
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face1_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace1810 A B C D E F G + piQuarticChamberRestLF1810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace1810, piQuarticChamberRestLF1810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·DD·DE·EE, CG·DD·DE·EE, CG·DD·DE·EE·CCC, CG·EE` (1 monomial, top degree `D.natDegree + E.natDegree`). -/
def kappaQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 4 (5 monomials). -/
def kappaQuarticChamberRestLF4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace4810 A B C D E F G + kappaQuarticChamberRestLF4810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace4810, kappaQuarticChamberRestLF4810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CF·DD·DF·FF, DD·DF·DG·FF·FG·GG, DD·DF·FF` (2 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 8 (8 monomials). -/
def muQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace8810 A B C D E F G + muQuarticChamberRestLF8810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace8810, muQuarticChamberRestLF8810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CF·DD·DF·FF, DD·DF·DG·FF·FG·GG, DD·DF·FF` (2 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 3 (11 monomials). -/
def xiQuarticChamberRestLF3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace3810 A B C D E F G + xiQuarticChamberRestLF3810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace3810, xiQuarticChamberRestLF3810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BG·CG·DD·BBB·BBC·BCC·CCC, DD·BBB·BBC·BCC·CCC` (1 monomial, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 4 (12 monomials). -/
def xiQuarticChamberRestLF4810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
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
theorem xiQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace4810 A B C D E F G + xiQuarticChamberRestLF4810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace4810, xiQuarticChamberRestLF4810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·CF·EE·BBB·BBC·BCC·CCC, EE·BBB·BBC·BCC·CCC` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (15 / 128 : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 5 (11 monomials). -/
def xiQuarticChamberRestLF5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace5810 A B C D E F G + xiQuarticChamberRestLF5810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace5810, xiQuarticChamberRestLF5810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `EE·CCC` (1 monomial, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 5 (5 monomials). -/
def kappaQuarticChamberRestLF5810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace5810 A B C D E F G + kappaQuarticChamberRestLF5810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace5810, kappaQuarticChamberRestLF5810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·CF·BBB·BBC·BCC·CCC, BF·CF·DD·BBB·BBC·BCC·CCC, BF·CF·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 6 (3 monomials). -/
def kappaQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace6810 A B C D E F G + kappaQuarticChamberRestLF6810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace6810, kappaQuarticChamberRestLF6810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·CF·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 9 (7 monomials). -/
def muQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace9810 A B C D E F G + muQuarticChamberRestLF9810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace9810, muQuarticChamberRestLF9810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·CF·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 6 (9 monomials). -/
def xiQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace6810 A B C D E F G + xiQuarticChamberRestLF6810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace6810, xiQuarticChamberRestLF6810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·EE·BBB, BG·BBB` (2 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 7 (4 monomials). -/
def kappaQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace7810 A B C D E F G + kappaQuarticChamberRestLF7810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace7810, kappaQuarticChamberRestLF7810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BG·BBB` (2 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 7 (11 monomials). -/
def xiQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace7810 A B C D E F G + xiQuarticChamberRestLF7810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace7810, xiQuarticChamberRestLF7810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 10 (7 monomials). -/
def muQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace10810 A B C D E F G + muQuarticChamberRestLF10810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace10810, muQuarticChamberRestLF10810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 8 (10 monomials). -/
def xiQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace8810 A B C D E F G + xiQuarticChamberRestLF8810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace8810, xiQuarticChamberRestLF8810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·CCC` (2 monomials, top degree `2 * B.natDegree + 2 * C.natDegree`). -/
def xiQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 9 (11 monomials). -/
def xiQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace9810 A B C D E F G + xiQuarticChamberRestLF9810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace9810, xiQuarticChamberRestLF9810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `DD·DE·EE·BBB` (1 monomial, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 10 (12 monomials). -/
def xiQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
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
theorem xiQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace10810 A B C D E F G + xiQuarticChamberRestLF10810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace10810, xiQuarticChamberRestLF10810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·CF·DD·DE·DF·EE·EF·FF, BF·CF·DD·DF·FF, BF·DD·DE·DF·EE·EF·FF, BF·DD·DF·FF` (1 monomial, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 2 (20 monomials). -/
def piQuarticChamberRestLF2810
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
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face2_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace2810 A B C D E F G + piQuarticChamberRestLF2810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace2810, piQuarticChamberRestLF2810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·BBB` (3 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace3810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 3 (18 monomials). -/
def piQuarticChamberRestLF3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
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

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face3_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace3810 A B C D E F G + piQuarticChamberRestLF3810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace3810, piQuarticChamberRestLF3810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·CCC, CG·EE·CCC` (2 monomials, top degree `2 * C.natDegree + E.natDegree`). -/
def xiQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 11 (11 monomials). -/
def xiQuarticChamberRestLF11810
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
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace11810 A B C D E F G + xiQuarticChamberRestLF11810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace11810, xiQuarticChamberRestLF11810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·EE, BG·CG·DD·DE·DG·EE·EG·GG, BG·CG·DD·DE·EE, BG·CG·EE·EG·GG` (1 monomial, top degree `E.natDegree + G.natDegree`). -/
def xiQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 12 (12 monomials). -/
def xiQuarticChamberRestLF12810
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
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace12810 A B C D E F G + xiQuarticChamberRestLF12810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace12810, xiQuarticChamberRestLF12810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CG·EE·CCC` (3 monomials, top degree `3 * C.natDegree`). -/
def muQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 11 (7 monomials). -/
def muQuarticChamberRestLF11810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace11810 A B C D E F G + muQuarticChamberRestLF11810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace11810, muQuarticChamberRestLF11810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CG·EE·CCC` (4 monomials, top degree `4 * C.natDegree`). -/
def piQuarticChamberFace4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 4 (17 monomials). -/
def piQuarticChamberRestLF4810
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
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face4_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace4810 A B C D E F G + piQuarticChamberRestLF4810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace4810, piQuarticChamberRestLF4810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `DD·CCC` (2 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 12 (8 monomials). -/
def muQuarticChamberRestLF12810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace12810 A B C D E F G + muQuarticChamberRestLF12810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace12810, muQuarticChamberRestLF12810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `DD·CCC` (2 monomials, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace5810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 5 (19 monomials). -/
def piQuarticChamberRestLF5810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face5_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace5810 A B C D E F G + piQuarticChamberRestLF5810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace5810, piQuarticChamberRestLF5810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 8 (3 monomials). -/
def kappaQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace8810 A B C D E F G + kappaQuarticChamberRestLF8810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace8810, kappaQuarticChamberRestLF8810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 128 : k) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 13 (6 monomials). -/
def muQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace13810 A B C D E F G + muQuarticChamberRestLF13810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace13810, muQuarticChamberRestLF13810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (6 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace6810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 6 (15 monomials). -/
def piQuarticChamberRestLF6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face6_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace6810 A B C D E F G + piQuarticChamberRestLF6810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace6810, piQuarticChamberRestLF6810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `DD·DE·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  - (15 / 128 : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 13 (10 monomials). -/
def xiQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace13810 A B C D E F G + xiQuarticChamberRestLF13810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace13810, xiQuarticChamberRestLF13810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·CF·DD·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 14 (6 monomials). -/
def muQuarticChamberRestLF14810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace14810 A B C D E F G + muQuarticChamberRestLF14810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace14810, muQuarticChamberRestLF14810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·CF·DD·BBB·BBC·BCC·CCC` (6 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace7810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 7 (15 monomials). -/
def piQuarticChamberRestLF7810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
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
theorem piQuarticLoadFree810_eq_face7_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace7810 A B C D E F G + piQuarticChamberRestLF7810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace7810, piQuarticChamberRestLF7810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC, BF·CF·DD·BBB·BBC·BCC·CCC, CG·DD·CCC` (2 monomials, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 14 (11 monomials). -/
def xiQuarticChamberRestLF14810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace14810 A B C D E F G + xiQuarticChamberRestLF14810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace14810, xiQuarticChamberRestLF14810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·DD, BF·BG·DD·BBB, BF·CF·DD·DE·EE, BF·DD` (1 monomial, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace15810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 15 (12 monomials). -/
def xiQuarticChamberRestLF15810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face15_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace15810 A B C D E F G + xiQuarticChamberRestLF15810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace15810, xiQuarticChamberRestLF15810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC, BG·CG·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 9 (3 monomials). -/
def kappaQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace9810 A B C D E F G + kappaQuarticChamberRestLF9810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace9810, kappaQuarticChamberRestLF9810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·CG·BBB·BBC·BCC·CCC` (6 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace8810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 8 (15 monomials). -/
def piQuarticChamberRestLF8810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face8_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace8810 A B C D E F G + piQuarticChamberRestLF8810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace8810, piQuarticChamberRestLF8810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·CF·EE·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace15810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 15 (6 monomials). -/
def muQuarticChamberRestLF15810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face15_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace15810 A B C D E F G + muQuarticChamberRestLF15810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace15810, muQuarticChamberRestLF15810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC, BG·CG·EE·BBB·BBC·BCC·CCC` (3 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace16810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 16 (10 monomials). -/
def xiQuarticChamberRestLF16810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face16_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace16810 A B C D E F G + xiQuarticChamberRestLF16810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace16810, xiQuarticChamberRestLF16810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CG·CCC` (2 monomials, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 10 (4 monomials). -/
def kappaQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace10810 A B C D E F G + kappaQuarticChamberRestLF10810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace10810, kappaQuarticChamberRestLF10810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 11 (2 monomials). -/
def kappaQuarticChamberRestLF11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace11810 A B C D E F G + kappaQuarticChamberRestLF11810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace11810, kappaQuarticChamberRestLF11810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (4 monomials, top degree `A.natDegree + 2 * B.natDegree + C.natDegree`). -/
def muQuarticChamberFace16810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 16 (6 monomials). -/
def muQuarticChamberRestLF16810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face16_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace16810 A B C D E F G + muQuarticChamberRestLF16810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace16810, muQuarticChamberRestLF16810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (8 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace9810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 9 (13 monomials). -/
def piQuarticChamberRestLF9810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face9_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace9810 A B C D E F G + piQuarticChamberRestLF9810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace9810, piQuarticChamberRestLF9810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·CF·CG·BBB·BBC·BCC·CCC` (5 monomials, top degree `A.natDegree + 4 * B.natDegree`). -/
def xiQuarticChamberFace17810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 17 (8 monomials). -/
def xiQuarticChamberRestLF17810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  - (5 / 64 : k) • (A * D * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face17_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace17810 A B C D E F G + xiQuarticChamberRestLF17810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace17810, xiQuarticChamberRestLF17810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·DD·DE·EE·BBB` (2 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 12 (4 monomials). -/
def kappaQuarticChamberRestLF12810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace12810 A B C D E F G + kappaQuarticChamberRestLF12810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace12810, kappaQuarticChamberRestLF12810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·BG·DD·DE·EE, BF·DD·DE·EE·BBB` (3 monomials, top degree `A.natDegree + B.natDegree + F.natDegree`). -/
def muQuarticChamberFace17810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 17 (7 monomials). -/
def muQuarticChamberRestLF17810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face17_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace17810 A B C D E F G + muQuarticChamberRestLF17810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace17810, muQuarticChamberRestLF17810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·DD·DE·EE·BBB` (3 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace10810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 16 : k) • (A * B * D * E)
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 10 (18 monomials). -/
def piQuarticChamberRestLF10810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face10_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace10810 A B C D E F G + piQuarticChamberRestLF10810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace10810, piQuarticChamberRestLF10810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·DD·DE·EE·BBB` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace18810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 18 (11 monomials). -/
def xiQuarticChamberRestLF18810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face18_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace18810 A B C D E F G + xiQuarticChamberRestLF18810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace18810, xiQuarticChamberRestLF18810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BG·DD·DE·EE·BBB` (3 monomials, top degree `A.natDegree + 3 * B.natDegree`). -/
def kappaQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 13 (3 monomials). -/
def kappaQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace13810 A B C D E F G + kappaQuarticChamberRestLF13810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace13810, kappaQuarticChamberRestLF13810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BG·DD·DE·EE·BBB` (4 monomials, top degree `2 * A.natDegree + 4 * B.natDegree`). -/
def piQuarticChamberFace11810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 11 (17 monomials). -/
def piQuarticChamberRestLF11810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
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

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face11_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace11810 A B C D E F G + piQuarticChamberRestLF11810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace11810, piQuarticChamberRestLF11810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·EE·BBB, BG·DD·DE·EE·BBB` (2 monomials, top degree `A.natDegree + 2 * B.natDegree + E.natDegree`). -/
def xiQuarticChamberFace19810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 19 (11 monomials). -/
def xiQuarticChamberRestLF19810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face19_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace19810 A B C D E F G + xiQuarticChamberRestLF19810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace19810, xiQuarticChamberRestLF19810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CF·DD·DE·EE·CCC, CG·DD·CCC` (2 monomials, top degree `C.natDegree + F.natDegree`). -/
def kappaQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 14 (4 monomials). -/
def kappaQuarticChamberRestLF14810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace14810 A B C D E F G + kappaQuarticChamberRestLF14810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace14810, kappaQuarticChamberRestLF14810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CF·DD·DE·EE·CCC` (3 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace18810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 18 (7 monomials). -/
def muQuarticChamberRestLF18810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face18_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace18810 A B C D E F G + muQuarticChamberRestLF18810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace18810, muQuarticChamberRestLF18810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CF·DD·DE·EE·CCC` (4 monomials, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace12810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 12 (17 monomials). -/
def piQuarticChamberRestLF12810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face12_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace12810 A B C D E F G + piQuarticChamberRestLF12810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace12810, piQuarticChamberRestLF12810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CF·DD·DE·EE·CCC` (2 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace20810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 20 (11 monomials). -/
def xiQuarticChamberRestLF20810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face20_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace20810 A B C D E F G + xiQuarticChamberRestLF20810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace20810, xiQuarticChamberRestLF20810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CG·DD·CCC, CG·EE·CCC` (3 monomials, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace15810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 15 (3 monomials). -/
def kappaQuarticChamberRestLF15810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face15_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace15810 A B C D E F G + kappaQuarticChamberRestLF15810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace15810, kappaQuarticChamberRestLF15810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CG·DD·CCC` (3 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace19810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 19 (7 monomials). -/
def muQuarticChamberRestLF19810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face19_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace19810 A B C D E F G + muQuarticChamberRestLF19810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace19810, muQuarticChamberRestLF19810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `CG·DD·CCC` (4 monomials, top degree `A.natDegree + C.natDegree + 2 * D.natDegree`). -/
def piQuarticChamberFace13810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (C ^ 2 * G)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 13 (17 monomials). -/
def piQuarticChamberRestLF13810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face13_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace13810 A B C D E F G + piQuarticChamberRestLF13810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace13810, piQuarticChamberRestLF13810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·DD·CCC` (3 monomials, top degree `A.natDegree + B.natDegree + C.natDegree + D.natDegree`). -/
def xiQuarticChamberFace21810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (A * B * C * D)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 21 (10 monomials). -/
def xiQuarticChamberRestLF21810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face21_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace21810 A B C D E F G + xiQuarticChamberRestLF21810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace21810, xiQuarticChamberRestLF21810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `BF·BG·CF·CG` (2 monomials, top degree `B.natDegree + G.natDegree`). -/
def kappaQuarticChamberFace16810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 16 (4 monomials). -/
def kappaQuarticChamberRestLF16810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face16_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace16810 A B C D E F G + kappaQuarticChamberRestLF16810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace16810, kappaQuarticChamberRestLF16810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `BF·BG·CF·CG` (2 monomials, top degree `A.natDegree + B.natDegree + F.natDegree`). -/
def muQuarticChamberFace20810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * B * F)
  + (5 / 16 : k) • (C * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 20 (8 monomials). -/
def muQuarticChamberRestLF20810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face20_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace20810 A B C D E F G + muQuarticChamberRestLF20810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace20810, muQuarticChamberRestLF20810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `π` on the argmin packet(s) `BF·BG·CF·CG, BF·BG·DD·DE·EE, CF·CG·DD·DE·EE` (2 monomials, top degree `A.natDegree + 2 * F.natDegree`). -/
def piQuarticChamberFace14810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `π` off packet 14 (19 monomials). -/
def piQuarticChamberRestLF14810
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
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticLoadFree810_eq_face14_add_rest
    (A B C D E F G : k[X]) :
    piQuarticLoadFree810 A B C D E F G =
      piQuarticChamberFace14810 A B C D E F G + piQuarticChamberRestLF14810 A B C D E F G := by
  simp only [piQuarticLoadFree810, piQuarticChamberFace14810, piQuarticChamberRestLF14810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `κ` on the argmin packet(s) `CG·DD·CCC, CG·EE·CCC` (3 monomials, top degree `B.natDegree + 2 * C.natDegree`). -/
def kappaQuarticChamberFace17810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `κ` off packet 17 (3 monomials). -/
def kappaQuarticChamberRestLF17810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  + (5 / 16 : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticLoadFree810_eq_face17_add_rest
    (A B C D E F G : k[X]) :
    kappaQuarticLoadFree810 A B C D E F G =
      kappaQuarticChamberFace17810 A B C D E F G + kappaQuarticChamberRestLF17810 A B C D E F G := by
  simp only [kappaQuarticLoadFree810, kappaQuarticChamberFace17810, kappaQuarticChamberRestLF17810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `BF·BG·DD·DE·EE, CF·CG·DD·DE·EE` (2 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace22810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 22 (11 monomials). -/
def xiQuarticChamberRestLF22810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face22_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace22810 A B C D E F G + xiQuarticChamberRestLF22810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace22810, xiQuarticChamberRestLF22810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `μ` on the argmin packet(s) `CF·CG·DD·DE·EE` (3 monomials, top degree `A.natDegree + 2 * D.natDegree`). -/
def muQuarticChamberFace21810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)
  + (5 / 16 : k) • (C * G)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `μ` off packet 21 (7 monomials). -/
def muQuarticChamberRestLF21810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)
  - (5 / 128 : k) • C ^ 3
  + (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticLoadFree810_eq_face21_add_rest
    (A B C D E F G : k[X]) :
    muQuarticLoadFree810 A B C D E F G =
      muQuarticChamberFace21810 A B C D E F G + muQuarticChamberRestLF21810 A B C D E F G := by
  simp only [muQuarticLoadFree810, muQuarticChamberFace21810, muQuarticChamberRestLF21810]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Face of `ξ` on the argmin packet(s) `CG·DD·CCC` (3 monomials, top degree `A.natDegree + D.natDegree + F.natDegree`). -/
def xiQuarticChamberFace23810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (A * D * F)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Load-free rest of `ξ` off packet 23 (10 monomials). -/
def xiQuarticChamberRestLF23810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticLoadFree810_eq_face23_add_rest
    (A B C D E F G : k[X]) :
    xiQuarticLoadFree810 A B C D E F G =
      xiQuarticChamberFace23810 A B C D E F G + xiQuarticChamberRestLF23810 A B C D E F G := by
  simp only [xiQuarticLoadFree810, xiQuarticChamberFace23810, xiQuarticChamberRestLF23810]
  all_goals try simp only [neg_smul]
  all_goals abel


end QuarticChamberFaces810

end Max11DegreeRoutes
/-! # Cost-argmin rest bounds, part 2/10, `(8,10)` scale zero

80 of the 655 load-free rest bounds, one per
(packet, live-letter set): the dead letters are `subst`-ed away and
each surviving monomial is below the face degree `d`, so the
chamber's ℕ conjuncts enter later by `omega`.  Depends only on
`Grok810ScaleZeroQuarticChamberFacesPart1Scratch`; the sibling `…Part*` modules are independent of each other,
so they gate in parallel.  Untracked working note.
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

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_B
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF0810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF0810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF0810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ B.natDegree + 2 * C.natDegree < d)
    (h2 : B = 0 ∨ G = 0 ∨ B.natDegree + G.natDegree < d)
    (h3 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h4 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_kappaQuarticChamberRestLF0810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BC
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hd0 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd3)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_kappaQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_C
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF0810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF0810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h4 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h6 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h7 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h8 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BC
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hGz))
    (Or.inl hDz)
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inl hDz)
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)
    (Or.inr (hd1))

def muQuarticChamberRestLF0810_liveBCDEF_p2c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEF_p2c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEF_p2c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEF_p2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEF_p2c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEF_p2c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def muQuarticChamberRestLF0810_liveBCDEF_p2c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 128 : k) • (B ^ 2 * E))
  - (15 / 64 : k) • (B * C * D)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEF_p2c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEF_p2c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 64) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEF_p2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEF_p2c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEF_p2c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEF_p2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (hd7))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inr (hd4)))
    (Or.inl hDz)
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))

def muQuarticChamberRestLF0810_liveBCDEFG_p2c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEFG_p2c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c1
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEFG_p2c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(5 / 128) : k), (-(15 / 128) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEFG_p2c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEFG_p2c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEFG_p2c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def muQuarticChamberRestLF0810_liveBCDEFG_p2c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 : k) • (B * C * D))
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF0810_liveBCDEFG_p2c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c2
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF0810_liveBCDEFG_p2c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF0810_liveBCDEFG_p2c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_liveBCDEFG_p2c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : C.natDegree + G.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810_liveBCDEFG_p2c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF0810_liveBCDEFG_p2c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF0810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : C.natDegree + G.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF0810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF0810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (hd8))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_D
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF1810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 2048 : k), (-(5 / 64) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(5 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF1810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (h1 : B = 0 ∨ 4 * B.natDegree < d)
    (h2 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h3 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h5 : C = 0 ∨ 3 * C.natDegree < d)
    (h6 : C = 0 ∨ G = 0 ∨ C.natDegree + G.natDegree < d)
    (h7 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h8 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart2_muQuarticChamberRestLF1810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * C.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (hd3))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inr (hd2))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inr (Or.inl hCz))
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + F.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF1810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF1810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart2_muQuarticChamberRestLF1810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hEz)


end QuarticChamberFaces810

end Max11DegreeRoutes
/-! # Cost-argmin rest bounds, part 7/10, `(8,10)` scale zero

80 of the 655 load-free rest bounds, one per
(packet, live-letter set): the dead letters are `subst`-ed away and
each surviving monomial is below the face degree `d`, so the
chamber's ℕ conjuncts enter later by `omega`.  Depends only on
`Grok810ScaleZeroQuarticChamberFacesPart1Scratch`; the sibling `…Part*` modules are independent of each other,
so they gate in parallel.  Untracked working note.
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

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF7810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_kappaQuarticChamberRestLF7810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF7810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `kappaQuarticChamberRestLF7810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ B.natDegree + 2 * C.natDegree < d)
    (h2 : C = 0 ∨ F = 0 ∨ C.natDegree + F.natDegree < d)
    (h3 : D = 0 ∨ E = 0 ∨ D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_kappaQuarticChamberRestLF7810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd2)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd1)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_kappaQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF7810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF7810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF7810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF7810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF7810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF7810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h4 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h9 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h10 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF7810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hDz))
    (Or.inl hEz)
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7810_natDegree_lt_of_live_BDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * B.natDegree + D.natDegree < d) :
    (xiQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7810_natDegree_lt_of_live_BFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hDz)
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hDz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hEz)
    (Or.inr (hd0))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF7810 A B C D E F G hdpos
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inl hDz)
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hDz))
    (Or.inl hEz)
    (Or.inr (hd2))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF10810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_muQuarticChamberRestLF10810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF10810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 64) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `muQuarticChamberRestLF10810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 4 * B.natDegree < d)
    (h1 : B = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + F.natDegree < d)
    (h2 : D = 0 ∨ A.natDegree + 2 * D.natDegree < d)
    (h3 : B = 0 ∨ E = 0 ∨ 2 * B.natDegree + E.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + C.natDegree + D.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ D.natDegree + F.natDegree < d)
    (h6 : E = 0 ∨ 2 * E.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_muQuarticChamberRestLF10810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd1))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inl hFz))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inr (hd2))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd1))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hFz))
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inl hEz)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inl hDz)
    (Or.inr (hd3))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF10810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_muQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF8810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (xiQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF8810` (10 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF8810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF8810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (15 / 256 : k), (55 / 1024 : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0],
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF8810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF8810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF8810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h6 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h8 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h9 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF8810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF8810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF8810 A B C D E F G hdpos
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inl hDz)
    (Or.inr (Or.inr (Or.inr (hd0))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hDz))
    (Or.inl hEz)
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF9810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF9810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF9810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF9810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF9810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF9810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h4 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h9 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h10 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF9810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d) :
    (xiQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF9810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inl hDz)
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hDz))
    (Or.inl hEz)
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF10810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF10810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h4 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h5 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h6 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h7 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h8 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h10 : E = 0 ∨ G = 0 ∨ E.natDegree + G.natDegree < d)
    (h11 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + E.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * C.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inl hGz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hGz))
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd4)))
    (Or.inl hFz)

def xiQuarticChamberRestLF10810_liveBCDEF_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810_liveBCDEF_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEF_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810_liveBCDEF_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF10810_liveBCDEF_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_liveBCDEF_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF10810_liveBCDEF_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEF_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF10810_liveBCDEF_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810_liveBCDEF_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEF_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810_liveBCDEF_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF10810_liveBCDEF_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_liveBCDEF_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810_liveBCDEF_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEF_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inl hGz))
    (Or.inr (hd9))

def xiQuarticChamberRestLF10810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810_liveBCDEG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810_liveBCDEG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF10810_liveBCDEG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_liveBCDEG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF10810_liveBCDEG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF10810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * D * E))
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810_liveBCDEG_p7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810_liveBCDEG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF10810_liveBCDEG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_liveBCDEG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF10810_liveBCDEG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd5)))
    (Or.inr (hd6))

def xiQuarticChamberRestLF10810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810_liveBCDEFG_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810_liveBCDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 256 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF10810_liveBCDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_liveBCDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF10810_liveBCDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF10810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF10810_liveBCDEFG_p7c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF10810_liveBCDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF10810_liveBCDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_liveBCDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810_liveBCDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF10810_liveBCDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF10810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF10810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (hd11))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810` (20 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810
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
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF2810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ 2 * A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ D = 0 ∨ A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ 4 * B.natDegree + C.natDegree < d)
    (h4 : B = 0 ∨ G = 0 ∨ A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (h5 : B = 0 ∨ C = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ D = 0 ∨ E = 0 ∨ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (h7 : C = 0 ∨ D = 0 ∨ A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (h8 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h9 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h10 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h11 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h12 : C = 0 ∨ 4 * C.natDegree < d)
    (h13 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h14 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h15 : C = 0 ∨ G = 0 ∨ 2 * C.natDegree + G.natDegree < d)
    (h16 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h17 : C = 0 ∨ E = 0 ∨ C.natDegree + 2 * E.natDegree < d)
    (h18 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d)
    (h19 : G = 0 ∨ 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h12 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h13 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h14 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h15 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h16 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h17 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h18 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h19 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inl hEz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))
    (Or.inl hGz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hGz)

def piQuarticChamberRestLF2810_liveBCDF_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDF_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDF_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDF_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 32 : k), (5 / 32 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 1, 1, 0, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDF_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDF_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDF_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDF_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBCDF_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDF_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDF_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDF_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(15 / 16) : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0],
      [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDF_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDF_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d)
    (hd10 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDF_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDF_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d)
    (hd10 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (hd9))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))
    (Or.inl hGz)

def piQuarticChamberRestLF2810_liveBCEF_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCEF_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEF_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCEF_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 32 : k), (25 / 128 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0],
      [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCEF_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCEF_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCEF_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEF_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBCEF_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (15 / 256 : k) • C ^ 4
  - (15 / 16 : k) • (B * E * F)
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCEF_p7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEF_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCEF_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (15 / 256 : k), (-(15 / 16) : k),
      (-(5 / 8) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 2, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCEF_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCEF_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 4 * C.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCEF_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEF_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 4 * C.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd6))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd8)))
    (Or.inl hDz)
    (Or.inl hGz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd6 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd6)))
    (Or.inl hGz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd6 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inl hEz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd4 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hDz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hDz)
    (Or.inr (hd4))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + 2 * E.natDegree < d)
    (hd4 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inl hGz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 2 * D.natDegree + E.natDegree < d)
    (hd1 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (hd1))

def piQuarticChamberRestLF2810_liveBCDEF_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEF_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEF_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEF_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 32 : k), (5 / 16 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEF_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEF_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEF_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEF_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBCDEF_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEF_p7c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEF_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEF_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32 : k), (25 / 128 : k), (45 / 64 : k),
      (45 / 128 : k), (45 / 64 : k), (15 / 256 : k)
      ]
      [
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEF_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEF_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd10 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd11 : 4 * C.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEF_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEF_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

def piQuarticChamberRestLF2810_liveBCDEF_p7c3
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (B * E * F))
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEF_p7c3` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEF_p7c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEF_p7c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 16) : k), (-(15 / 16) : k), (-(5 / 8) : k),
      (-(5 / 8) : k)
      ]
      [
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEF_p7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEF_p7c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd14 : C.natDegree + 2 * E.natDegree < d)
    (hd15 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEF_p7c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEF_p7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    by simpa only [Nat.add_assoc] using hd15,
    lt_of_le_of_lt (Nat.zero_le _) hd12⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd10 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd11 : 4 * C.natDegree < d)
    (hd12 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd14 : C.natDegree + 2 * E.natDegree < d)
    (hd15 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (hd11))
    (Or.inr (Or.inr (Or.inl hGz)))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inl hGz))
    (Or.inr (Or.inr (Or.inr (hd13))))
    (Or.inr (Or.inr (hd14)))
    (Or.inr (Or.inr (hd15)))
    (Or.inl hGz)

def piQuarticChamberRestLF2810_liveBCDFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDFG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBCDFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDFG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 1, 0, 0, 1, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

def piQuarticChamberRestLF2810_liveBCDFG_p7c3
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDFG_p7c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDFG_p7c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDFG_p7c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 256 : k), (-(5 / 8) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (5 / 4 : k)
      ]
      [
      [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDFG_p7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDFG_p7c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 4 * C.natDegree < d)
    (hd11 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd12 : 2 * C.natDegree + G.natDegree < d)
    (hd13 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDFG_p7c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDFG_p7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : 4 * C.natDegree < d)
    (hd11 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd12 : 2 * C.natDegree + G.natDegree < d)
    (hd13 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (hd10))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd12)))
    (Or.inr (Or.inr (Or.inr (hd13))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))
    (Or.inr (hd14))

def piQuarticChamberRestLF2810_liveBCEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCEFG_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 64 : k), (5 / 32 : k), (25 / 128 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1],
      [1, 1, 1, 0, 0, 1, 0], [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBCEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (15 / 256 : k) • C ^ 4
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCEFG_p7c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (15 / 256 : k), (-(15 / 16) : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 4 * C.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : 2 * C.natDegree + G.natDegree < d)
    (hd10 : C.natDegree + 2 * E.natDegree < d)
    (hd11 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 4 * C.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : 2 * C.natDegree + G.natDegree < d)
    (hd10 : C.natDegree + 2 * E.natDegree < d)
    (hd11 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd7))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd10)))
    (Or.inl hDz)
    (Or.inr (hd11))

def piQuarticChamberRestLF2810_liveBDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBDEFG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBDEFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (5 / 64 : k),
      (5 / 16 : k), (25 / 128 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0],
      [0, 3, 0, 0, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBDEFG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBDEFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd8)))
    (Or.inr (hd9))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : 2 * C.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : C.natDegree + 2 * E.natDegree < d)
    (hd5 : 2 * D.natDegree + E.natDegree < d)
    (hd6 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (hd1))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (hd6))

def piQuarticChamberRestLF2810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEFG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF2810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEFG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32 : k), (5 / 16 : k), (5 / 32 : k),
      (25 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + F.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

def piQuarticChamberRestLF2810_liveBCDEFG_p7c3
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEFG_p7c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEFG_p7c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 128 : k), (45 / 64 : k), (15 / 256 : k),
      (-(5 / 8) : k), (-(15 / 16) : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1],
      [0, 1, 0, 0, 1, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEFG_p7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEFG_p7c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd11 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd12 : 4 * C.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEFG_p7c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

def piQuarticChamberRestLF2810_liveBCDEFG_p7c4
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (C ^ 2 * G))
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF2810_liveBCDEFG_p7c4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c4
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF2810_liveBCDEFG_p7c4 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(15 / 16) : k), (-(5 / 8) : k),
      (-(5 / 8) : k), (5 / 4 : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0],
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF2810_liveBCDEFG_p7c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_liveBCDEFG_p7c4_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd15 : 2 * C.natDegree + G.natDegree < d)
    (hd16 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd17 : C.natDegree + 2 * E.natDegree < d)
    (hd18 : 2 * D.natDegree + E.natDegree < d)
    (hd19 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810_liveBCDEFG_p7c4 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF2810_liveBCDEFG_p7c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd15,
    by simpa only [Nat.add_assoc] using hd16,
    by simpa only [Nat.add_assoc] using hd17,
    by simpa only [Nat.add_assoc] using hd18,
    by simpa only [Nat.add_assoc] using hd19,
    lt_of_le_of_lt (Nat.zero_le _) hd15⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF2810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + F.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd11 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd12 : 4 * C.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : 2 * C.natDegree + G.natDegree < d)
    (hd16 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd17 : C.natDegree + 2 * E.natDegree < d)
    (hd18 : 2 * D.natDegree + E.natDegree < d)
    (hd19 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF2810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF2810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (Or.inr (Or.inr (hd11))))
    (Or.inr (hd12))
    (Or.inr (Or.inr (Or.inr (hd13))))
    (Or.inr (Or.inr (Or.inr (hd14))))
    (Or.inr (Or.inr (hd15)))
    (Or.inr (Or.inr (Or.inr (hd16))))
    (Or.inr (Or.inr (hd17)))
    (Or.inr (Or.inr (hd18)))
    (Or.inr (hd19))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

def piQuarticChamberRestLF3810_liveBCDG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810` (18 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 32 : k), (5 / 16 : k), (5 / 32 : k),
      (25 / 128 : k), (45 / 64 : k), (45 / 128 : k),
      (45 / 64 : k), (15 / 256 : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0],
      [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0],
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `piQuarticChamberRestLF3810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ D = 0 ∨ A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (h1 : B = 0 ∨ C = 0 ∨ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ 4 * B.natDegree + C.natDegree < d)
    (h3 : B = 0 ∨ C = 0 ∨ F = 0 ∨ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (h4 : B = 0 ∨ D = 0 ∨ E = 0 ∨ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (h5 : C = 0 ∨ D = 0 ∨ A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (h6 : B = 0 ∨ F = 0 ∨ 3 * B.natDegree + F.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ E = 0 ∨ 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (h8 : B = 0 ∨ D = 0 ∨ 2 * B.natDegree + 2 * D.natDegree < d)
    (h9 : B = 0 ∨ C = 0 ∨ D = 0 ∨ B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (h10 : C = 0 ∨ 4 * C.natDegree < d)
    (h11 : F = 0 ∨ A.natDegree + 2 * F.natDegree < d)
    (h12 : B = 0 ∨ D = 0 ∨ G = 0 ∨ B.natDegree + D.natDegree + G.natDegree < d)
    (h13 : B = 0 ∨ E = 0 ∨ F = 0 ∨ B.natDegree + E.natDegree + F.natDegree < d)
    (h14 : C = 0 ∨ G = 0 ∨ 2 * C.natDegree + G.natDegree < d)
    (h15 : C = 0 ∨ D = 0 ∨ F = 0 ∨ C.natDegree + D.natDegree + F.natDegree < d)
    (h16 : C = 0 ∨ E = 0 ∨ C.natDegree + 2 * E.natDegree < d)
    (h17 : D = 0 ∨ E = 0 ∨ 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h12 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h13 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h14 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h15 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h16 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h17 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 32 : k), (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF3810_liveBCDG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDG_p7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (15 / 256 : k), (-(5 / 8) : k),
      (-(5 / 16) : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : 4 * C.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : 4 * C.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (hd6))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : 4 * C.natDegree < d)
    (hd4 : 2 * C.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd3))
    (Or.inl hFz)
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd5)))
    (Or.inl hDz)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd4 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inl hCz)
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd4)))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 3 * B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd3 : A.natDegree + 2 * F.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (hd3))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hEz))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inl hEz))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hd0 : 3 * B.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + 2 * F.natDegree < d)
    (hd2 : B.natDegree + E.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hDz))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (hd1))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hDz)

def piQuarticChamberRestLF3810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDEG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDEG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDEG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDEG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDEG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF3810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 8 : k) • (B * D * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDEG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDEG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 8) : k)
      ]
      [
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDEG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDEG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : 4 * C.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDEG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

def piQuarticChamberRestLF3810_liveBCDEG_p7c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (C ^ 2 * G))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDEG_p7c3` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEG_p7c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDEG_p7c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDEG_p7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDEG_p7c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDEG_p7c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEG_p7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : 4 * C.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (hd8))
    (Or.inl hFz)
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (hd11)))
    (Or.inr (Or.inr (hd12)))

def piQuarticChamberRestLF3810_liveBCDFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDFG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 32 : k), (5 / 32 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0],
      [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF3810_liveBCDFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDFG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 16) : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : 4 * C.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

def piQuarticChamberRestLF3810_liveBCDFG_p7c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDFG_p7c3` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDFG_p7c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDFG_p7c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8) : k), (-(5 / 16) : k), (-(15 / 16) : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDFG_p7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDFG_p7c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDFG_p7c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDFG_p7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    by simpa only [Nat.add_assoc] using hd12,
    lt_of_le_of_lt (Nat.zero_le _) hd10⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : 4 * C.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inl hEz)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (hd8))
    (Or.inr (hd9))
    (Or.inr (Or.inr (Or.inr (hd10))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inr (hd11)))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inl hEz))
    (Or.inr (Or.inl hEz))

def piQuarticChamberRestLF3810_liveBCEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  -((45 / 512 : k) • (A * B ^ 2 * C ^ 2))
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCEFG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCEFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 512) : k), (-(35 / 256) : k), (5 / 32 : k),
      (25 / 128 : k), (45 / 64 : k)
      ]
      [
      [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [0, 3, 0, 0, 0, 1, 0],
      [0, 2, 1, 0, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF3810_liveBCEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (C * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCEFG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCEFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 256 : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 0, 2, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 4 * C.natDegree < d)
    (hd6 : A.natDegree + 2 * F.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : 2 * C.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 4 * C.natDegree < d)
    (hd6 : A.natDegree + 2 * F.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : 2 * C.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (hd5))
    (Or.inr (hd6))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd9)))
    (Or.inl hDz)

def piQuarticChamberRestLF3810_liveBDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBDEFG_p7c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBDEFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k), (25 / 128 : k),
      (45 / 128 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF3810_liveBDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBDEFG_p7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBDEFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(5 / 8) : k)
      ]
      [
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd7 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd7 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd1))))
    (Or.inl hCz)
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inl hCz)
    (Or.inr (hd4))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (Or.inr (hd7)))

def piQuarticChamberRestLF3810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDEFG_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 32 : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0],
      [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def piQuarticChamberRestLF3810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDEFG_p7c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 128 : k), (45 / 64 : k), (45 / 128 : k),
      (45 / 64 : k), (15 / 256 : k), (-(5 / 16) : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : 4 * C.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

def piQuarticChamberRestLF3810_liveBCDEFG_p7c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF3810_liveBCDEFG_p7c3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEFG_p7c3
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF3810_liveBCDEFG_p7c3 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF3810_liveBCDEFG_p7c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_liveBCDEFG_p7c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810_liveBCDEFG_p7c3 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_piQuarticChamberRestLF3810_liveBCDEFG_p7c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd12,
    by simpa only [Nat.add_assoc] using hd13,
    by simpa only [Nat.add_assoc] using hd14,
    by simpa only [Nat.add_assoc] using hd15,
    by simpa only [Nat.add_assoc] using hd16,
    by simpa only [Nat.add_assoc] using hd17,
    lt_of_le_of_lt (Nat.zero_le _) hd12⟩

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF3810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : 4 * C.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF3810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_piQuarticChamberRestLF3810 A B C D E F G hdpos
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inr (Or.inr (hd3))))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (hd8)))
    (Or.inr (Or.inr (Or.inr (hd9))))
    (Or.inr (hd10))
    (Or.inr (hd11))
    (Or.inr (Or.inr (Or.inr (hd12))))
    (Or.inr (Or.inr (Or.inr (hd13))))
    (Or.inr (Or.inr (hd14)))
    (Or.inr (Or.inr (Or.inr (hd15))))
    (Or.inr (Or.inr (hd16)))
    (Or.inr (Or.inr (hd17)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (xiQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF11810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

def xiQuarticChamberRestLF11810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF11810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF11810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF11810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF11810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF11810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h8 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h10 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF11810_liveBCDEG_p7c1` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF11810_liveBCDEG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF11810_liveBCDEG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_liveBCDEG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d) :
    (xiQuarticChamberRestLF11810_liveBCDEG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF11810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF11810_liveBCDEG_p7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF11810_liveBCDEG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 : k), (-(5 / 64) : k), (-(25 / 128) : k),
      (-(15 / 128) : k)
      ]
      [
      [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF11810_liveBCDEG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_liveBCDEG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF11810_liveBCDEG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    lt_of_le_of_lt (Nat.zero_le _) hd4⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF11810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF11810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inl hDz))
    (Or.inr (hd5))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF11810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (hd2))

def xiQuarticChamberRestLF11810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF11810_liveBCDEFG_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF11810_liveBCDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF11810_liveBCDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_liveBCDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF11810_liveBCDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF11810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF11810_liveBCDEFG_p7c2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF11810_liveBCDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0],
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF11810_liveBCDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_liveBCDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF11810_liveBCDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF11810_liveBCDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF11810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF11810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (hd10))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF12810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF12810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF12810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel

set_option maxHeartbeats 64000000 in
/-- Shared zero-or-degree certificate for `xiQuarticChamberRestLF12810`. -/
private theorem facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (h0 : B = 0 ∨ A.natDegree + 4 * B.natDegree < d)
    (h1 : B = 0 ∨ E = 0 ∨ A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (h2 : B = 0 ∨ C = 0 ∨ D = 0 ∨ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (h3 : B = 0 ∨ D = 0 ∨ 3 * B.natDegree + D.natDegree < d)
    (h4 : B = 0 ∨ C = 0 ∨ 2 * B.natDegree + 2 * C.natDegree < d)
    (h5 : D = 0 ∨ F = 0 ∨ A.natDegree + D.natDegree + F.natDegree < d)
    (h6 : B = 0 ∨ G = 0 ∨ 2 * B.natDegree + G.natDegree < d)
    (h7 : B = 0 ∨ C = 0 ∨ F = 0 ∨ B.natDegree + C.natDegree + F.natDegree < d)
    (h8 : B = 0 ∨ D = 0 ∨ E = 0 ∨ B.natDegree + D.natDegree + E.natDegree < d)
    (h9 : C = 0 ∨ E = 0 ∨ 2 * C.natDegree + E.natDegree < d)
    (h10 : C = 0 ∨ D = 0 ∨ C.natDegree + 2 * D.natDegree < d)
    (h11 : F = 0 ∨ 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810]
  apply Max11ReflectDeg.natDegree_polyOf_lt_of_degOk hdpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · rcases h0 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h1 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h2 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h3 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (3 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h4 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h5 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h6 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h7 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h8 with hz0 | hz1 | hz2 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz2, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h9 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h10 with hz0 | hz1 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (1 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz1, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb
  · rcases h11 with hz0 | hb
    · apply Or.inr; apply Or.inl
      simp only [Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left,
        Max11ReflectDeg.mono_nil_right, hz0, pow_zero, pow_one,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, one_mul, mul_one]
    · apply Or.inr; apply Or.inr
      simpa only [Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
        Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.add_assoc] using hb


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hDz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_DEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hFz))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : 2 * C.natDegree + E.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hDz))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_BDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_CDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inl hFz))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inr (hd1)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_CEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hDz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inr (Or.inl hDz))
    (Or.inr (hd1))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (hd1))

def xiQuarticChamberRestLF12810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF12810_liveBCDEG_p7c1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEG_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF12810_liveBCDEG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF12810_liveBCDEG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_liveBCDEG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF12810_liveBCDEG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF12810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF12810_liveBCDEG_p7c2` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEG_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF12810_liveBCDEG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [xiQuarticChamberRestLF12810_liveBCDEG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_liveBCDEG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF12810_liveBCDEG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd5,
    by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    lt_of_le_of_lt (Nat.zero_le _) hd5⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hFz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (Or.inl hFz)))
    (Or.inr (Or.inr (Or.inr (hd6))))
    (Or.inr (Or.inr (hd7)))
    (Or.inr (Or.inr (hd8)))
    (Or.inl hFz)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 2 * C.natDegree + E.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inl hDz)))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd2)))
    (Or.inl hDz)
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (Or.inr (hd4))))
    (Or.inr (Or.inl hDz))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inl hDz))
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inl hCz))
    (Or.inr (Or.inr (Or.inr (hd5))))
    (Or.inl hCz)
    (Or.inl hCz)
    (Or.inr (hd6))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd0)))
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inl hBz)
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (hd2)))
    (Or.inr (hd3))

def xiQuarticChamberRestLF12810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF12810_liveBCDEFG_p7c1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEFG_p7c1
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF12810_liveBCDEFG_p7c1 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF12810_liveBCDEFG_p7c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_liveBCDEFG_p7c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF12810_liveBCDEFG_p7c1 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEFG_p7c1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd0,
    by simpa only [Nat.add_assoc] using hd1,
    by simpa only [Nat.add_assoc] using hd2,
    by simpa only [Nat.add_assoc] using hd3,
    by simpa only [Nat.add_assoc] using hd4,
    by simpa only [Nat.add_assoc] using hd5,
    lt_of_le_of_lt (Nat.zero_le _) hd0⟩

def xiQuarticChamberRestLF12810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF12810_liveBCDEFG_p7c2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEFG_p7c2
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF12810_liveBCDEFG_p7c2 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF12810_liveBCDEFG_p7c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals try simp only [neg_smul]
  all_goals abel


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_liveBCDEFG_p7c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : 2 * C.natDegree + E.natDegree < d)
    (hd10 : C.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810_liveBCDEFG_p7c2 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberFacesPart7_xiQuarticChamberRestLF12810_liveBCDEFG_p7c2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  exact ⟨by simpa only [Nat.add_assoc] using hd6,
    by simpa only [Nat.add_assoc] using hd7,
    by simpa only [Nat.add_assoc] using hd8,
    by simpa only [Nat.add_assoc] using hd9,
    by simpa only [Nat.add_assoc] using hd10,
    by simpa only [Nat.add_assoc] using hd11,
    lt_of_le_of_lt (Nat.zero_le _) hd6⟩

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : 2 * C.natDegree + E.natDegree < d)
    (hd10 : C.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  exact facesRound4SpeedTBound_ChamberFacesPart7_xiQuarticChamberRestLF12810 A B C D E F G hdpos
    (Or.inr (hd0))
    (Or.inr (Or.inr (hd1)))
    (Or.inr (Or.inr (Or.inr (hd2))))
    (Or.inr (Or.inr (hd3)))
    (Or.inr (Or.inr (hd4)))
    (Or.inr (Or.inr (hd5)))
    (Or.inr (Or.inr (hd6)))
    (Or.inr (Or.inr (Or.inr (hd7))))
    (Or.inr (Or.inr (Or.inr (hd8))))
    (Or.inr (Or.inr (hd9)))
    (Or.inr (Or.inr (hd10)))
    (Or.inr (hd11))


end QuarticChamberFaces810

end Max11DegreeRoutes
