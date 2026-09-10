import Grok810ScaleZeroQuarticChamberUnownedPacketsScratch
import Max11SpeedReflectDegLibScratch

/-! # Unowned load-column bounds, part 4/5

42 of the 222 (carrier, load, live-set) column bounds the
kills need, including the columns of `N₂, N₃, N₅, N₆`.  A column
with more than twelve surviving monomials is split first, so no
single `compute_degree` sees more than ten.  Independent of its
siblings.  Untracked note.
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

section QuarticChamberUnownedColumns4810

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnGamma810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnGamma810
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
theorem n5QuarticColumnGamma810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (n5QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnGamma810]
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
/-- Piece 1/2 of `n5QuarticColumnDelta810` on the live set `BDEFG` (6 monomials). -/
def n5QuarticColumnDelta810PartBDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810PartBDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810PartBDEFG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * delta : k), (-(5 / 16384 * delta) : k), (15 / 1024 * delta : k),
      (5 / 512 * delta : k), (5 / 64 * delta : k), (-(5 / 64 * delta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticColumnDelta810PartBDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartBDEFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + F.natDegree < d) :
    (n5QuarticColumnDelta810PartBDEFG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnDelta810` on the live set `BDEFG` (1 monomials). -/
def n5QuarticColumnDelta810PartBDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 * delta : k)) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810PartBDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810PartBDEFG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128 * delta) : k)
      ]
      [
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810PartBDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartBDEFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree < d) :
    (n5QuarticColumnDelta810PartBDEFG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_split_of_live_BDEFG
    (delta : k)
    (A B C D E F G : k[X])
    (hCz : C = 0) :
    n5QuarticColumnDelta810 delta A B C D E F G =
      n5QuarticColumnDelta810PartBDEFG1810 delta A B C D E F G +
        n5QuarticColumnDelta810PartBDEFG2810 delta A B C D E F G := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnDelta810, n5QuarticColumnDelta810PartBDEFG1810, n5QuarticColumnDelta810PartBDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + F.natDegree < d)
    (hd6 : 2 * D.natDegree < d) :
    (n5QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnDelta810_split_of_live_BDEFG delta A B C D E F G hCz]
  exact (natDegree_add_lt810 (n5QuarticColumnDelta810PartBDEFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnDelta810PartBDEFG2810_natDegree_lt delta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnEpsilon810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEpsilon810
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
theorem n5QuarticColumnEpsilon810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 3 * B.natDegree < d)
    (hd1 : B.natDegree + E.natDegree < d) :
    (n5QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEpsilon810]
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
/-- Reflected monomial data for `n5QuarticColumnZeta810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * zeta : k), (3 / 256 * zeta : k), (3 / 1024 * zeta : k),
      (3 / 64 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k),
      (3 / 8 * zeta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n5QuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree < d)
    (hd2 : A.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n5QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810]
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
/-- Reflected monomial data for `n5QuarticColumnEta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEta810
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
theorem n5QuarticColumnEta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : F.natDegree < d) :
    (n5QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEta810]
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
/-- Reflected monomial data for `n5QuarticColumnTheta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnTheta810
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
theorem n5QuarticColumnTheta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d)
    (hd2 : E.natDegree < d) :
    (n5QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnTheta810]
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
/-- Piece 1/2 of `n5QuarticColumnL1810` on the live set `CDEFG` (6 monomials). -/
def n5QuarticColumnL1810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  + (315 / 262144 * l : k) • (A ^ 4 * E)
  + (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * G)
  + (27 / 4096 * l : k) • (A ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810PartCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (429 / 33554432 * l : k), (315 / 1048576 * l : k), (315 / 262144 * l : k),
      (135 / 131072 * l : k), (45 / 8192 * l : k), (27 / 4096 * l : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 0, 1], [2, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + E.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + G.natDegree < d)
    (hd5 : 2 * A.natDegree + C.natDegree + E.natDegree < d) :
    (n5QuarticColumnL1810PartCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnL1810` on the live set `CDEFG` (5 monomials). -/
def n5QuarticColumnL1810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 16384 * l : k)) • (A ^ 2 * D ^ 2)
  - (3 / 2048 * l : k) • (A * C ^ 3)
  + (9 / 256 * l : k) • (A * C * G)
  - (9 / 512 * l : k) • (A * D * F)
  + (9 / 1024 * l : k) • (A * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810PartCDEFG2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810PartCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 16384 * l) : k), (-(3 / 2048 * l) : k), (9 / 256 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k)
      ]
      [
      [2, 0, 0, 2, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0],
      [1, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd1 : A.natDegree + 3 * C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + 2 * E.natDegree < d) :
    (n5QuarticColumnL1810PartCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_split_of_live_CDEFG
    (l : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n5QuarticColumnL1810 l A B C D E F G =
      n5QuarticColumnL1810PartCDEFG1810 l A B C D E F G +
        n5QuarticColumnL1810PartCDEFG2810 l A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnL1810, n5QuarticColumnL1810PartCDEFG1810, n5QuarticColumnL1810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + E.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + G.natDegree < d)
    (hd5 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd7 : A.natDegree + 3 * C.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd9 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : A.natDegree + 2 * E.natDegree < d) :
    (n5QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnL1810_split_of_live_CDEFG l A B C D E F G hBz]
  exact (natDegree_add_lt810 (n5QuarticColumnL1810PartCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnL1810PartCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL2810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL2810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k), (9 / 64 * l : k),
      (9 / 128 * l : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n5QuarticColumnL2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (n5QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL2810]
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
/-- Piece 1/2 of `n5QuarticColumnBeta810` on the live set `CDEFG` (6 monomials). -/
def n5QuarticColumnBeta810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  + (7 / 1024 * beta : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * beta : k), (35 / 32768 * beta : k), (35 / 8192 * beta : k),
      (21 / 16384 * beta : k), (21 / 1024 * beta : k), (7 / 1024 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d) :
    (n5QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnBeta810` on the live set `CDEFG` (3 monomials). -/
def n5QuarticColumnBeta810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810PartCDEFG2810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 512 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (n5QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_split_of_live_CDEFG
    (beta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n5QuarticColumnBeta810 beta A B C D E F G =
      n5QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G +
        n5QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnBeta810, n5QuarticColumnBeta810PartCDEFG1810, n5QuarticColumnBeta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * C.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (n5QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnBeta810_split_of_live_CDEFG beta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n5QuarticColumnBeta810PartCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnBeta810PartCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnGamma810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + F.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (n5QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnGamma810]
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
/-- Piece 1/2 of `n5QuarticColumnDelta810` on the live set `CDEFG` (6 monomials). -/
def n5QuarticColumnDelta810PartCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  - (5 / 1024 * delta : k) • (A * C ^ 2)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 32 * delta : k) • (C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * delta : k), (15 / 4096 * delta : k), (15 / 1024 * delta : k),
      (-(5 / 1024 * delta) : k), (5 / 64 * delta : k), (-(5 / 32 * delta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree < d) :
    (n5QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnDelta810` on the live set `CDEFG` (1 monomials). -/
def n5QuarticColumnDelta810PartCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 * delta : k)) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810PartCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128 * delta) : k)
      ]
      [
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree < d) :
    (n5QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_split_of_live_CDEFG
    (delta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n5QuarticColumnDelta810 delta A B C D E F G =
      n5QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G +
        n5QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnDelta810, n5QuarticColumnDelta810PartCDEFG1810, n5QuarticColumnDelta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree < d)
    (hd6 : 2 * D.natDegree < d) :
    (n5QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnDelta810_split_of_live_CDEFG delta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n5QuarticColumnDelta810PartCDEFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnDelta810PartCDEFG2810_natDegree_lt delta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + D.natDegree < d) :
    (n5QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEpsilon810]
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
theorem n5QuarticColumnZeta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n5QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810]
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
theorem n5QuarticColumnEta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : F.natDegree < d) :
    (n5QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEta810]
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
theorem n5QuarticColumnTheta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : E.natDegree < d) :
    (n5QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnTheta810]
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
/-- Piece 1/2 of `n2QuarticColumnL810` on the live set `CDEFG` (6 monomials). -/
def n2QuarticColumnL810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  + (9 / 512 * l : k) • (A * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * l : k), (315 / 262144 * l : k), (45 / 8192 * l : k),
      (27 / 16384 * l : k), (27 / 1024 * l : k), (9 / 512 * l : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + E.natDegree < d) :
    (n2QuarticColumnL810PartCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n2QuarticColumnL810` on the live set `CDEFG` (5 monomials). -/
def n2QuarticColumnL810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 1024 * l : k)) • (A * D ^ 2)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartCDEFG2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 1024 * l) : k), (-(21 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [1, 0, 0, 2, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810PartCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_split_of_live_CDEFG
    (l : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n2QuarticColumnL810 l A B C D E F G =
      n2QuarticColumnL810PartCDEFG1810 l A B C D E F G +
        n2QuarticColumnL810PartCDEFG2810 l A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnL810, n2QuarticColumnL810PartCDEFG1810, n2QuarticColumnL810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + 2 * D.natDegree < d)
    (hd7 : 3 * C.natDegree < d)
    (hd8 : C.natDegree + G.natDegree < d)
    (hd9 : D.natDegree + F.natDegree < d)
    (hd10 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [n2QuarticColumnL810_split_of_live_CDEFG l A B C D E F G hBz]
  exact (natDegree_add_lt810 (n2QuarticColumnL810PartCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnL810PartCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n2QuarticColumnBeta810` on the live set `CDEFG` (6 monomials). -/
def n2QuarticColumnBeta810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  - (7 / 1024 * beta : k) • (A * C ^ 2)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * beta : k), (35 / 8192 * beta : k), (21 / 1024 * beta : k),
      (-(7 / 1024 * beta) : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree < d) :
    (n2QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n2QuarticColumnBeta810` on the live set `CDEFG` (1 monomials). -/
def n2QuarticColumnBeta810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 128 * beta : k)) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810PartCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 128 * beta) : k)
      ]
      [
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_split_of_live_CDEFG
    (beta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n2QuarticColumnBeta810 beta A B C D E F G =
      n2QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G +
        n2QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnBeta810, n2QuarticColumnBeta810PartCDEFG1810, n2QuarticColumnBeta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree < d)
    (hd6 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n2QuarticColumnBeta810_split_of_live_CDEFG beta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n2QuarticColumnBeta810PartCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnBeta810PartCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnGamma810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnGamma810
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
theorem n2QuarticColumnGamma810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + D.natDegree < d) :
    (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnGamma810]
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
/-- Reflected monomial data for `n2QuarticColumnDelta810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * delta : k), (15 / 1024 * delta : k), (15 / 1024 * delta : k),
      (5 / 64 * delta : k), (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k),
      (5 / 8 * delta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n2QuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnDelta810]
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
/-- Reflected monomial data for `n2QuarticColumnEpsilon810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnEpsilon810
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
theorem n2QuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : F.natDegree < d) :
    (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnEpsilon810]
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
/-- Reflected monomial data for `n2QuarticColumnZeta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnZeta810
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
theorem n2QuarticColumnZeta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : E.natDegree < d) :
    (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnZeta810]
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
/-- Reflected monomial data for `n2QuarticColumnEta810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnEta810
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
theorem n2QuarticColumnEta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : D.natDegree < d) :
    (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnEta810]
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
/-- Reflected monomial data for `n2QuarticColumnTheta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnTheta810
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
theorem n2QuarticColumnTheta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnTheta810]
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
/-- Piece 1/4 of `n5QuarticColumnL1810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnL1810PartBCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  - (225 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (315 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 65536 * l : k) • (A ^ 3 * B * D)
  + (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810PartBCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (429 / 33554432 * l : k), (315 / 1048576 * l : k), (-(225 / 4194304 * l) : k),
      (315 / 262144 * l : k), (-(27 / 65536 * l) : k), (135 / 131072 * l : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d) :
    (n5QuarticColumnL1810PartBCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/4 of `n5QuarticColumnL1810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnL1810PartBCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 65536 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (441 / 262144 * l : k) • (A * B ^ 4)
  + (45 / 8192 * l : k) • (A ^ 3 * G)
  - (27 / 8192 * l : k) • (A ^ 2 * B * F)
  + (27 / 4096 * l : k) • (A ^ 2 * C * E)
  - (9 / 16384 * l : k) • (A ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810PartBCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 65536 * l : k), (-(441 / 262144 * l) : k), (45 / 8192 * l : k),
      (-(27 / 8192 * l) : k), (27 / 4096 * l : k), (-(9 / 16384 * l) : k)
      ]
      [
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0],
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 4 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + G.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * D.natDegree < d) :
    (n5QuarticColumnL1810PartBCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/4 of `n5QuarticColumnL1810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnL1810PartBCDEFG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 8192 * l : k) • (A * B ^ 2 * E)
  + (9 / 1024 * l : k) • (A * B * C * D)
  - (3 / 2048 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 256 * l : k) • (A * C * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810PartBCDEFG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG3810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810PartBCDEFG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 8192 * l : k), (9 / 1024 * l : k), (-(3 / 2048 * l) : k),
      (189 / 8192 * l : k), (567 / 16384 * l : k), (9 / 256 * l : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1]
      ] := by
  simp only [n5QuarticColumnL1810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + G.natDegree < d) :
    (n5QuarticColumnL1810PartBCDEFG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/4 of `n5QuarticColumnL1810` on the live set `BCDEFG` (2 monomials). -/
def n5QuarticColumnL1810PartBCDEFG4810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 512 * l : k)) • (A * D * F)
  + (9 / 1024 * l : k) • (A * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL1810PartBCDEFG4810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG4810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810PartBCDEFG4810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 512 * l) : k), (9 / 1024 * l : k)
      ]
      [
      [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n5QuarticColumnL1810PartBCDEFG4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + 2 * E.natDegree < d) :
    (n5QuarticColumnL1810PartBCDEFG4810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL1810PartBCDEFG4810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_split_of_live_BCDEFG
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL1810 l A B C D E F G =
      n5QuarticColumnL1810PartBCDEFG1810 l A B C D E F G +
        n5QuarticColumnL1810PartBCDEFG2810 l A B C D E F G +
        n5QuarticColumnL1810PartBCDEFG3810 l A B C D E F G +
        n5QuarticColumnL1810PartBCDEFG4810 l A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnL1810, n5QuarticColumnL1810PartBCDEFG1810, n5QuarticColumnL1810PartBCDEFG2810, n5QuarticColumnL1810PartBCDEFG3810, n5QuarticColumnL1810PartBCDEFG4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  rw [n5QuarticColumnL1810_split_of_live_BCDEFG l A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticColumnL1810PartBCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnL1810PartBCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n5QuarticColumnL1810PartBCDEFG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (n5QuarticColumnL1810PartBCDEFG4810_natDegree_lt l A B C D E F G hdpos hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n5QuarticColumnL2810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnL2810PartBCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 1024 * l : k)) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL2810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL2810PartBCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL2810PartBCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k), (-(45 / 512 * l) : k),
      (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k), (9 / 64 * l : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0],
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1]
      ] := by
  simp only [n5QuarticColumnL2810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d) :
    (n5QuarticColumnL2810PartBCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL2810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnL2810` on the live set `BCDEFG` (1 monomials). -/
def n5QuarticColumnL2810PartBCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 128 * l : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnL2810PartBCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL2810PartBCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL2810PartBCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 128 * l : k)
      ]
      [
      [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n5QuarticColumnL2810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * F.natDegree < d) :
    (n5QuarticColumnL2810PartBCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnL2810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_split_of_live_BCDEFG
    (l : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnL2810 l A B C D E F G =
      n5QuarticColumnL2810PartBCDEFG1810 l A B C D E F G +
        n5QuarticColumnL2810PartBCDEFG2810 l A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnL2810, n5QuarticColumnL2810PartBCDEFG1810, n5QuarticColumnL2810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (n5QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnL2810_split_of_live_BCDEFG l A B C D E F G]
  exact (natDegree_add_lt810 (n5QuarticColumnL2810PartBCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnL2810PartBCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n5QuarticColumnBeta810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnBeta810PartBCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartBCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810PartBCDEFG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * beta : k), (35 / 32768 * beta : k), (-(21 / 131072 * beta) : k),
      (35 / 8192 * beta : k), (-(7 / 8192 * beta) : k), (21 / 16384 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n5QuarticColumnBeta810PartBCDEFG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n5QuarticColumnBeta810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnBeta810PartBCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 2048 * beta : k)) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartBCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810PartBCDEFG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 2048 * beta) : k), (-(189 / 32768 * beta) : k), (21 / 1024 * beta : k),
      (-(7 / 512 * beta) : k), (7 / 1024 * beta : k), (35 / 1024 * beta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * B.natDegree + E.natDegree < d) :
    (n5QuarticColumnBeta810PartBCDEFG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n5QuarticColumnBeta810` on the live set `BCDEFG` (4 monomials). -/
def n5QuarticColumnBeta810PartBCDEFG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnBeta810PartBCDEFG3810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartBCDEFG3810
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810PartBCDEFG3810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n5QuarticColumnBeta810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (n5QuarticColumnBeta810PartBCDEFG3810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnBeta810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_split_of_live_BCDEFG
    (beta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnBeta810 beta A B C D E F G =
      n5QuarticColumnBeta810PartBCDEFG1810 beta A B C D E F G +
        n5QuarticColumnBeta810PartBCDEFG2810 beta A B C D E F G +
        n5QuarticColumnBeta810PartBCDEFG3810 beta A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnBeta810, n5QuarticColumnBeta810PartBCDEFG1810, n5QuarticColumnBeta810PartBCDEFG2810, n5QuarticColumnBeta810PartBCDEFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  rw [n5QuarticColumnBeta810_split_of_live_BCDEFG beta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticColumnBeta810PartBCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnBeta810PartBCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n5QuarticColumnBeta810PartBCDEFG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13 hd14 hd15))

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnGamma810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : C.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + E.natDegree < d) :
    (n5QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnGamma810]
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
/-- Piece 1/2 of `n5QuarticColumnDelta810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnDelta810PartBCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810PartBCDEFG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * delta : k), (15 / 4096 * delta : k), (-(5 / 16384 * delta) : k),
      (15 / 1024 * delta : k), (5 / 512 * delta : k), (-(5 / 1024 * delta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n5QuarticColumnDelta810PartBCDEFG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnDelta810` on the live set `BCDEFG` (5 monomials). -/
def n5QuarticColumnDelta810PartBCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnDelta810PartBCDEFG2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810PartBCDEFG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 * delta : k), (5 / 64 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnDelta810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + G.natDegree < d)
    (hd2 : B.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + E.natDegree < d)
    (hd4 : 2 * D.natDegree < d) :
    (n5QuarticColumnDelta810PartBCDEFG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnDelta810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_split_of_live_BCDEFG
    (delta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnDelta810 delta A B C D E F G =
      n5QuarticColumnDelta810PartBCDEFG1810 delta A B C D E F G +
        n5QuarticColumnDelta810PartBCDEFG2810 delta A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnDelta810, n5QuarticColumnDelta810PartBCDEFG1810, n5QuarticColumnDelta810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  rw [n5QuarticColumnDelta810_split_of_live_BCDEFG delta A B C D E F G]
  exact (natDegree_add_lt810 (n5QuarticColumnDelta810PartBCDEFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnDelta810PartBCDEFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree < d)
    (hd1 : B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + D.natDegree < d) :
    (n5QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEpsilon810]
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
/-- Piece 1/2 of `n5QuarticColumnZeta810` on the live set `BCDEFG` (6 monomials). -/
def n5QuarticColumnZeta810PartBCDEFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnZeta810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810PartBCDEFG1810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810PartBCDEFG1810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * zeta : k), (3 / 256 * zeta : k), (3 / 1024 * zeta : k),
      (3 / 64 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticColumnZeta810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d) :
    (n5QuarticColumnZeta810PartBCDEFG1810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnZeta810` on the live set `BCDEFG` (1 monomials). -/
def n5QuarticColumnZeta810PartBCDEFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * zeta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticColumnZeta810PartBCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810PartBCDEFG2810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810PartBCDEFG2810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * zeta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n5QuarticColumnZeta810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : G.natDegree < d) :
    (n5QuarticColumnZeta810PartBCDEFG2810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnZeta810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_split_of_live_BCDEFG
    (zeta : k)
    (A B C D E F G : k[X]) :
    n5QuarticColumnZeta810 zeta A B C D E F G =
      n5QuarticColumnZeta810PartBCDEFG1810 zeta A B C D E F G +
        n5QuarticColumnZeta810PartBCDEFG2810 zeta A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnZeta810, n5QuarticColumnZeta810PartBCDEFG1810, n5QuarticColumnZeta810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n5QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnZeta810_split_of_live_BCDEFG zeta A B C D E F G]
  exact (natDegree_add_lt810 (n5QuarticColumnZeta810PartBCDEFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnZeta810PartBCDEFG2810_natDegree_lt zeta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (n5QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnEta810]
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
theorem n5QuarticColumnTheta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (n5QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n5QuarticColumnTheta810]
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
/-- Piece 1/3 of `n2QuarticColumnL810` on the live set `BCDEFG` (6 monomials). -/
def n2QuarticColumnL810PartBCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartBCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * l : k), (315 / 262144 * l : k), (-(9 / 131072 * l) : k),
      (45 / 8192 * l : k), (-(9 / 8192 * l) : k), (27 / 16384 * l : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n2QuarticColumnL810PartBCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n2QuarticColumnL810` on the live set `BCDEFG` (6 monomials). -/
def n2QuarticColumnL810PartBCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * B * F)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartBCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 8192 * l : k), (315 / 32768 * l : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 512 * l : k), (-(9 / 1024 * l) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d) :
    (n2QuarticColumnL810PartBCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n2QuarticColumnL810` on the live set `BCDEFG` (6 monomials). -/
def n2QuarticColumnL810PartBCDEFG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(63 / 1024 * l : k)) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartBCDEFG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEFG3810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartBCDEFG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + E.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * C.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810PartBCDEFG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_split_of_live_BCDEFG
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810 l A B C D E F G =
      n2QuarticColumnL810PartBCDEFG1810 l A B C D E F G +
        n2QuarticColumnL810PartBCDEFG2810 l A B C D E F G +
        n2QuarticColumnL810PartBCDEFG3810 l A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnL810, n2QuarticColumnL810PartBCDEFG1810, n2QuarticColumnL810PartBCDEFG2810, n2QuarticColumnL810PartBCDEFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  rw [n2QuarticColumnL810_split_of_live_BCDEFG l A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n2QuarticColumnL810PartBCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnL810PartBCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n2QuarticColumnL810PartBCDEFG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n2QuarticColumnBeta810` on the live set `BCDEFG` (6 monomials). -/
def n2QuarticColumnBeta810PartBCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810PartBCDEFG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * beta : k), (35 / 8192 * beta : k), (7 / 16384 * beta : k),
      (21 / 1024 * beta : k), (7 / 512 * beta : k), (-(7 / 1024 * beta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n2QuarticColumnBeta810PartBCDEFG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n2QuarticColumnBeta810` on the live set `BCDEFG` (5 monomials). -/
def n2QuarticColumnBeta810PartBCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810PartBCDEFG2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810PartBCDEFG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + G.natDegree < d)
    (hd2 : B.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + E.natDegree < d)
    (hd4 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810PartBCDEFG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_split_of_live_BCDEFG
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810 beta A B C D E F G =
      n2QuarticColumnBeta810PartBCDEFG1810 beta A B C D E F G +
        n2QuarticColumnBeta810PartBCDEFG2810 beta A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnBeta810, n2QuarticColumnBeta810PartBCDEFG1810, n2QuarticColumnBeta810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  rw [n2QuarticColumnBeta810_split_of_live_BCDEFG beta A B C D E F G]
  exact (natDegree_add_lt810 (n2QuarticColumnBeta810PartBCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnBeta810PartBCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnGamma810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree < d)
    (hd1 : B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + D.natDegree < d) :
    (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnGamma810]
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
/-- Piece 1/2 of `n2QuarticColumnDelta810` on the live set `BCDEFG` (6 monomials). -/
def n2QuarticColumnDelta810PartBCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * delta : k) • A ^ 4
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnDelta810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnDelta810PartBCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810PartBCDEFG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * delta : k), (15 / 1024 * delta : k), (15 / 1024 * delta : k),
      (5 / 64 * delta : k), (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnDelta810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d) :
    (n2QuarticColumnDelta810PartBCDEFG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnDelta810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n2QuarticColumnDelta810` on the live set `BCDEFG` (1 monomials). -/
def n2QuarticColumnDelta810PartBCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 8 * delta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnDelta810PartBCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnDelta810PartBCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810PartBCDEFG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 8 * delta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n2QuarticColumnDelta810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : G.natDegree < d) :
    (n2QuarticColumnDelta810PartBCDEFG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnDelta810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810_split_of_live_BCDEFG
    (delta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnDelta810 delta A B C D E F G =
      n2QuarticColumnDelta810PartBCDEFG1810 delta A B C D E F G +
        n2QuarticColumnDelta810PartBCDEFG2810 delta A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnDelta810, n2QuarticColumnDelta810PartBCDEFG1810, n2QuarticColumnDelta810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnDelta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n2QuarticColumnDelta810_split_of_live_BCDEFG delta A B C D E F G]
  exact (natDegree_add_lt810 (n2QuarticColumnDelta810PartBCDEFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnDelta810PartBCDEFG2810_natDegree_lt delta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnEpsilon810]
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
theorem n2QuarticColumnZeta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnZeta810]
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
theorem n2QuarticColumnEta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : D.natDegree < d) :
    (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnEta810]
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
theorem n2QuarticColumnTheta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnTheta810]
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
/-- Piece 1/3 of `n2QuarticColumnL810` on the live set `BCDEG` (6 monomials). -/
def n2QuarticColumnL810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * l : k) • A ^ 6
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * l : k), (315 / 262144 * l : k), (-(9 / 131072 * l) : k),
      (45 / 8192 * l : k), (-(9 / 8192 * l) : k), (27 / 16384 * l : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n2QuarticColumnL810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n2QuarticColumnL810` on the live set `BCDEG` (6 monomials). -/
def n2QuarticColumnL810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 8192 * l : k), (315 / 32768 * l : k), (27 / 1024 * l : k),
      (9 / 512 * l : k), (-(9 / 1024 * l) : k), (-(63 / 1024 * l) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * B.natDegree + E.natDegree < d) :
    (n2QuarticColumnL810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n2QuarticColumnL810` on the live set `BCDEG` (4 monomials). -/
def n2QuarticColumnL810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(63 / 512 * l : k)) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnL810PartBCDEG3810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnL810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 128 * l : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n2QuarticColumnL810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnL810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n2QuarticColumnL810 l A B C D E F G =
      n2QuarticColumnL810PartBCDEG1810 l A B C D E F G +
        n2QuarticColumnL810PartBCDEG2810 l A B C D E F G +
        n2QuarticColumnL810PartBCDEG3810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnL810, n2QuarticColumnL810PartBCDEG1810, n2QuarticColumnL810PartBCDEG2810, n2QuarticColumnL810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnL810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 4 * B.natDegree < d)
    (hd8 : 2 * A.natDegree + G.natDegree < d)
    (hd9 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : A.natDegree + 2 * D.natDegree < d)
    (hd11 : 2 * B.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd13 : 3 * C.natDegree < d)
    (hd14 : C.natDegree + G.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [n2QuarticColumnL810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n2QuarticColumnL810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnL810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n2QuarticColumnL810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n2QuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def n2QuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810PartBCDEG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 262144 * beta : k), (35 / 8192 * beta : k), (7 / 16384 * beta : k),
      (21 / 1024 * beta : k), (7 / 512 * beta : k), (-(7 / 1024 * beta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n2QuarticColumnBeta810PartBCDEG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n2QuarticColumnBeta810` on the live set `BCDEG` (4 monomials). -/
def n2QuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticColumnBeta810PartBCDEG2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n2QuarticColumnBeta810PartBCDEG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (63 / 1024 * beta : k), (7 / 64 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n2QuarticColumnBeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + E.natDegree < d)
    (hd3 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810PartBCDEG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedColumns4_n2QuarticColumnBeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_split_of_live_BCDEG
    (beta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n2QuarticColumnBeta810 beta A B C D E F G =
      n2QuarticColumnBeta810PartBCDEG1810 beta A B C D E F G +
        n2QuarticColumnBeta810PartBCDEG2810 beta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticColumnBeta810, n2QuarticColumnBeta810PartBCDEG1810, n2QuarticColumnBeta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n2QuarticColumnBeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + E.natDegree < d)
    (hd9 : 2 * D.natDegree < d) :
    (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n2QuarticColumnBeta810_split_of_live_BCDEG beta A B C D E F G hFz]
  exact (natDegree_add_lt810 (n2QuarticColumnBeta810PartBCDEG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n2QuarticColumnBeta810PartBCDEG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9))


end QuarticChamberUnownedColumns4810

end Max11DegreeRoutes
