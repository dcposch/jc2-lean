import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch
import Max11SpeedReflectDegLibScratch

/-! # UnownedSystem load-column bounds, part 5/10

33 of the 403 (carrier, load, live-set) column bounds the
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

section QuarticChamberUnownedSystemColumns5810

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n3QuarticColumnBeta810` on the live set `CDEFG` (6 monomials). -/
def n3QuarticColumnBeta810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2097152 * beta : k) • A ^ 6
  + (35 / 131072 * beta : k) • (A ^ 4 * C)
  + (7 / 16384 * beta : k) • (A ^ 3 * E)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  + (21 / 1024 * beta : k) • (A * C * E)
  + (35 / 2048 * beta : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 2097152 * beta : k), (35 / 131072 * beta : k), (7 / 16384 * beta : k),
      (21 / 8192 * beta : k), (21 / 1024 * beta : k), (35 / 2048 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d) :
    (n3QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n3QuarticColumnBeta810` on the live set `CDEFG` (3 monomials). -/
def n3QuarticColumnBeta810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810PartCDEFG2810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 512 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (n3QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_split_of_live_CDEFG
    (beta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n3QuarticColumnBeta810 beta A B C D E F G =
      n3QuarticColumnBeta810PartCDEFG1810 beta A B C D E F G +
        n3QuarticColumnBeta810PartCDEFG2810 beta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnBeta810, n3QuarticColumnBeta810PartCDEFG1810, n3QuarticColumnBeta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * C.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnBeta810_split_of_live_CDEFG beta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n3QuarticColumnBeta810PartCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnBeta810PartCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnGamma810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(23 / 2048 * gamma) : k), (9 / 256 * gamma : k), (9 / 256 * gamma : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k),
      (-(3 / 16 * gamma) : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnGamma810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnGamma810]
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
/-- Reflected monomial data for `n3QuarticColumnDelta810` (10 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnDelta810
    (delta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnDelta810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 524288 * delta : k), (15 / 16384 * delta : k), (-(25 / 8192 * delta) : k),
      (55 / 1024 * delta : k), (35 / 2048 * delta : k), (45 / 512 * delta : k),
      (-(5 / 128 * delta) : k), (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k),
      (-(15 / 128 * delta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + E.natDegree < d)
    (hd5 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnDelta810]
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
/-- Reflected monomial data for `n3QuarticColumnEpsilon810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnEpsilon810
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
theorem n3QuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree < d) :
    (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnEpsilon810]
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
/-- Reflected monomial data for `n3QuarticColumnZeta810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnZeta810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnZeta810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32768 * zeta : k), (3 / 1024 * zeta : k), (51 / 2048 * zeta : k),
      (-(3 / 128 * zeta) : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k),
      (3 / 8 * zeta : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n3QuarticColumnZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_natDegree_lt_of_live_CDEFG
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
    (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnZeta810]
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
/-- Reflected monomial data for `n3QuarticColumnEta810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnEta810
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
theorem n3QuarticColumnEta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : F.natDegree < d) :
    (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnEta810]
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
/-- Reflected monomial data for `n3QuarticColumnTheta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnTheta810
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
theorem n3QuarticColumnTheta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : E.natDegree < d) :
    (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnTheta810]
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
/-- Piece 1/2 of `n4QuarticColumnL1810` on the live set `CDEFG` (6 monomials). -/
def n4QuarticColumnL1810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8
  + (315 / 4194304 * l : k) • (A ^ 6 * C)
  + (45 / 131072 * l : k) • (A ^ 5 * E)
  + (459 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  + (9 / 32768 * l : k) • (A ^ 4 * G)
  + (9 / 1024 * l : k) • (A ^ 3 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810PartCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (495 / 268435456 * l : k), (315 / 4194304 * l : k), (45 / 131072 * l : k),
      (459 / 524288 * l : k), (9 / 32768 * l : k), (9 / 1024 * l : k)
      ]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0], [4, 0, 2, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 1], [3, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + E.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 4 * A.natDegree + G.natDegree < d)
    (hd5 : 3 * A.natDegree + C.natDegree + E.natDegree < d) :
    (n4QuarticColumnL1810PartCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnL1810` on the live set `CDEFG` (5 monomials). -/
def n4QuarticColumnL1810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 4096 * l : k)) • (A ^ 3 * D ^ 2)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  + (9 / 1024 * l : k) • (A ^ 2 * C * G)
  + (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810PartCDEFG2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810PartCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 4096 * l) : k), (9 / 16384 * l : k), (9 / 1024 * l : k),
      (9 / 512 * l : k), (27 / 1024 * l : k)
      ]
      [
      [3, 0, 0, 2, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0],
      [2, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd3 : 2 * A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810PartCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_split_of_live_CDEFG
    (l : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n4QuarticColumnL1810 l A B C D E F G =
      n4QuarticColumnL1810PartCDEFG1810 l A B C D E F G +
        n4QuarticColumnL1810PartCDEFG2810 l A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL1810, n4QuarticColumnL1810PartCDEFG1810, n4QuarticColumnL1810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + E.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 4 * A.natDegree + G.natDegree < d)
    (hd5 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd8 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd9 : 2 * A.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnL1810_split_of_live_CDEFG l A B C D E F G hBz]
  exact (natDegree_add_lt810 (n4QuarticColumnL1810PartCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL1810PartCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnL2810` on the live set `CDEFG` (6 monomials). -/
def n4QuarticColumnL2810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 512 * l : k) • (A * C ^ 2 * E)
  + (45 / 512 * l : k) • (A * C * D ^ 2)
  + (63 / 4096 * l : k) • C ^ 4
  - (27 / 128 * l : k) • (A * F ^ 2)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810PartCDEFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 512 * l : k), (45 / 512 * l : k), (63 / 4096 * l : k),
      (-(27 / 128 * l) : k), (-(9 / 128 * l) : k), (-(9 / 32 * l) : k)
      ]
      [
      [1, 0, 2, 0, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0],
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0]
      ] := by
  simp only [n4QuarticColumnL2810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * F.natDegree < d)
    (hd4 : 2 * C.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + D.natDegree + F.natDegree < d) :
    (n4QuarticColumnL2810PartCDEFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnL2810` on the live set `CDEFG` (3 monomials). -/
def n4QuarticColumnL2810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 64 * l : k)) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810PartCDEFG2810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810PartCDEFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k), (9 / 16 * l : k)
      ]
      [
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [n4QuarticColumnL2810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + 2 * E.natDegree < d)
    (hd1 : 2 * D.natDegree + E.natDegree < d)
    (hd2 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810PartCDEFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_split_of_live_CDEFG
    (l : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n4QuarticColumnL2810 l A B C D E F G =
      n4QuarticColumnL2810PartCDEFG1810 l A B C D E F G +
        n4QuarticColumnL2810PartCDEFG2810 l A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL2810, n4QuarticColumnL2810PartCDEFG1810, n4QuarticColumnL2810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * F.natDegree < d)
    (hd4 : 2 * C.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * E.natDegree < d)
    (hd7 : 2 * D.natDegree + E.natDegree < d)
    (hd8 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnL2810_split_of_live_CDEFG l A B C D E F G hBz]
  exact (natDegree_add_lt810 (n4QuarticColumnL2810PartCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL2810PartCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnBeta1810` on the live set `CDEFG` (6 monomials). -/
def n4QuarticColumnBeta1810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7
  + (35 / 131072 * beta : k) • (A ^ 5 * C)
  + (21 / 16384 * beta : k) • (A ^ 4 * E)
  + (21 / 8192 * beta : k) • (A ^ 3 * C ^ 2)
  + (7 / 256 * beta : k) • (A ^ 2 * C * E)
  - (7 / 256 * beta : k) • (A ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810PartCDEFG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 2097152 * beta : k), (35 / 131072 * beta : k), (21 / 16384 * beta : k),
      (21 / 8192 * beta : k), (7 / 256 * beta : k), (-(7 / 256 * beta) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + E.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * D.natDegree < d) :
    (n4QuarticColumnBeta1810PartCDEFG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnBeta1810` on the live set `CDEFG` (4 monomials). -/
def n4QuarticColumnBeta1810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 512 * beta : k)) • (A * C ^ 3)
  + (7 / 64 * beta : k) • (A * D * F)
  + (21 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810PartCDEFG2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810PartCDEFG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 512 * beta) : k), (7 / 64 * beta : k), (21 / 128 * beta : k),
      (7 / 64 * beta : k)
      ]
      [
      [1, 0, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * C.natDegree < d)
    (hd1 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 2 * E.natDegree < d)
    (hd3 : 2 * C.natDegree + E.natDegree < d) :
    (n4QuarticColumnBeta1810PartCDEFG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_split_of_live_CDEFG
    (beta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n4QuarticColumnBeta1810 beta A B C D E F G =
      n4QuarticColumnBeta1810PartCDEFG1810 beta A B C D E F G +
        n4QuarticColumnBeta1810PartCDEFG2810 beta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta1810, n4QuarticColumnBeta1810PartCDEFG1810, n4QuarticColumnBeta1810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + E.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd6 : A.natDegree + 3 * C.natDegree < d)
    (hd7 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * C.natDegree + E.natDegree < d) :
    (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnBeta1810_split_of_live_CDEFG beta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n4QuarticColumnBeta1810PartCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnBeta1810PartCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta2810
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
theorem n4QuarticColumnBeta2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta2810]
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
/-- Reflected monomial data for `n4QuarticColumnGamma810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnGamma810
    (gamma : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnGamma810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 2048 * gamma : k), (-(3 / 256 * gamma) : k), (-(3 / 256 * gamma) : k),
      (-(9 / 64 * gamma) : k), (-(3 / 32 * gamma) : k), (-(27 / 256 * gamma) : k),
      (3 / 8 * gamma : k), (9 / 64 * gamma : k), (3 / 8 * gamma : k),
      (3 / 16 * gamma : k), (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [n4QuarticColumnGamma810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 2 * C.natDegree + D.natDegree < d)
    (hd3 : E.natDegree + F.natDegree < d) :
    (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnGamma810]
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
/-- Piece 1/2 of `n4QuarticColumnDelta810` on the live set `CDEFG` (6 monomials). -/
def n4QuarticColumnDelta810PartCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6
  + (15 / 16384 * delta : k) • (A ^ 4 * C)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  + (5 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  + (15 / 64 * delta : k) • (A * C * E)
  + (25 / 128 * delta : k) • (A * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 262144 * delta : k), (15 / 16384 * delta : k), (5 / 1024 * delta : k),
      (5 / 1024 * delta : k), (15 / 64 * delta : k), (25 / 128 * delta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0, 0],
      [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d) :
    (n4QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnDelta810` on the live set `CDEFG` (3 monomials). -/
def n4QuarticColumnDelta810PartCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810PartCDEFG2810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 64 * delta : k), (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_split_of_live_CDEFG
    (delta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n4QuarticColumnDelta810 delta A B C D E F G =
      n4QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G +
        n4QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnDelta810, n4QuarticColumnDelta810PartCDEFG1810, n4QuarticColumnDelta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * C.natDegree < d)
    (hd7 : D.natDegree + F.natDegree < d)
    (hd8 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnDelta810_split_of_live_CDEFG delta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n4QuarticColumnDelta810PartCDEFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnDelta810PartCDEFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEpsilon810` (9 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEpsilon810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 64 * epsilon) : k), (-(1 / 16 * epsilon) : k), (1 / 32 * epsilon : k),
      (1 / 4 * epsilon : k), (1 / 4 * epsilon : k), (7 / 32 * epsilon : k),
      (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k), (-(1 / 2 * epsilon) : k)
      ]
      [
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0],
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnEpsilon810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * A.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d)
    (hd3 : D.natDegree + E.natDegree < d) :
    (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEpsilon810]
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
/-- Piece 1/2 of `n4QuarticColumnZeta810` on the live set `CDEFG` (6 monomials). -/
def n4QuarticColumnZeta810PartCDEFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5
  + (3 / 1024 * zeta : k) • (A ^ 3 * C)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (9 / 128 * zeta : k) • (A * C ^ 2)
  - (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnZeta810PartCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnZeta810PartCDEFG1810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810PartCDEFG1810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32768 * zeta : k), (3 / 1024 * zeta : k), (3 / 128 * zeta : k),
      (9 / 128 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnZeta810PartCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree < d) :
    (n4QuarticColumnZeta810PartCDEFG1810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnZeta810PartCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnZeta810` on the live set `CDEFG` (1 monomials). -/
def n4QuarticColumnZeta810PartCDEFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * zeta : k)) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnZeta810PartCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnZeta810PartCDEFG2810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810PartCDEFG2810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * zeta) : k)
      ]
      [
      [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnZeta810PartCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree < d) :
    (n4QuarticColumnZeta810PartCDEFG2810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnZeta810PartCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_split_of_live_CDEFG
    (zeta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n4QuarticColumnZeta810 zeta A B C D E F G =
      n4QuarticColumnZeta810PartCDEFG1810 zeta A B C D E F G +
        n4QuarticColumnZeta810PartCDEFG2810 zeta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnZeta810, n4QuarticColumnZeta810PartCDEFG1810, n4QuarticColumnZeta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (zeta : k)
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
    (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnZeta810_split_of_live_CDEFG zeta A B C D E F G hBz]
  exact (natDegree_add_lt810 (n4QuarticColumnZeta810PartCDEFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnZeta810PartCDEFG2810_natDegree_lt zeta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEta810
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
theorem n4QuarticColumnEta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + F.natDegree < d)
    (hd2 : C.natDegree + D.natDegree < d) :
    (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEta810]
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
/-- Reflected monomial data for `n4QuarticColumnTheta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnTheta810
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
theorem n4QuarticColumnTheta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * C.natDegree < d)
    (hd3 : G.natDegree < d) :
    (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnTheta810]
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
/-- Piece 1/4 of `n3QuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (165 / 67108864 * l : k) • A ^ 7
  + (315 / 4194304 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (45 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 131072 * l : k) • (A ^ 3 * B * D)
  + (189 / 262144 * l : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (165 / 67108864 * l : k), (315 / 4194304 * l : k), (-(171 / 4194304 * l) : k),
      (45 / 262144 * l : k), (-(27 / 131072 * l) : k), (189 / 262144 * l : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnL1810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDEG1810_natDegree_lt
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
    (n3QuarticColumnL1810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/4 of `n3QuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(171 / 131072 * l : k)) • (A ^ 2 * B ^ 2 * C)
  - (1827 / 524288 * l : k) • (A * B ^ 4)
  + (9 / 16384 * l : k) • (A ^ 3 * G)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (9 / 8192 * l : k) • (A ^ 2 * D ^ 2)
  + (243 / 16384 * l : k) • (A * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(171 / 131072 * l) : k), (-(1827 / 524288 * l) : k), (9 / 16384 * l : k),
      (27 / 8192 * l : k), (9 / 8192 * l : k), (243 / 16384 * l : k)
      ]
      [
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n3QuarticColumnL1810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 4 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + G.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + E.natDegree < d) :
    (n3QuarticColumnL1810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/4 of `n3QuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (261 / 8192 * l : k) • (A * B * C * D)
  + (39 / 16384 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 1024 * l : k) • (A * C * G)
  - (9 / 2048 * l : k) • (A * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810PartBCDEG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (261 / 8192 * l : k), (39 / 16384 * l : k), (189 / 8192 * l : k),
      (567 / 16384 * l : k), (9 / 1024 * l : k), (-(9 / 2048 * l) : k)
      ]
      [
      [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n3QuarticColumnL1810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 3 * C.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + 2 * E.natDegree < d) :
    (n3QuarticColumnL1810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/4 of `n3QuarticColumnL1810` on the live set `BCDEG` (1 monomials). -/
def n3QuarticColumnL1810PartBCDEG4810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 1024 * l : k)) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL1810PartBCDEG4810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG4810
    (l : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnL1810PartBCDEG4810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 1024 * l) : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [n3QuarticColumnL1810PartBCDEG4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDEG4810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + G.natDegree < d) :
    (n3QuarticColumnL1810PartBCDEG4810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL1810PartBCDEG4810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n3QuarticColumnL1810 l A B C D E F G =
      n3QuarticColumnL1810PartBCDEG1810 l A B C D E F G +
        n3QuarticColumnL1810PartBCDEG2810 l A B C D E F G +
        n3QuarticColumnL1810PartBCDEG3810 l A B C D E F G +
        n3QuarticColumnL1810PartBCDEG4810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnL1810, n3QuarticColumnL1810PartBCDEG1810, n3QuarticColumnL1810PartBCDEG2810, n3QuarticColumnL1810PartBCDEG3810, n3QuarticColumnL1810PartBCDEG4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
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
    (hd17 : A.natDegree + 2 * E.natDegree < d)
    (hd18 : 2 * B.natDegree + G.natDegree < d) :
    (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnL1810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n3QuarticColumnL1810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnL1810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n3QuarticColumnL1810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (n3QuarticColumnL1810PartBCDEG4810_natDegree_lt l A B C D E F G hdpos hd18))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnL2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL2810
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
theorem n3QuarticColumnL2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * D.natDegree < d)
    (hd3 : E.natDegree + G.natDegree < d) :
    (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnL2810]
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
/-- Piece 1/3 of `n3QuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2097152 * beta : k) • A ^ 6
  + (35 / 131072 * beta : k) • (A ^ 4 * C)
  - (63 / 262144 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 16384 * beta : k) • (A ^ 3 * E)
  - (7 / 2048 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810PartBCDEG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 2097152 * beta : k), (35 / 131072 * beta : k), (-(63 / 262144 * beta) : k),
      (7 / 16384 * beta : k), (-(7 / 2048 * beta) : k), (21 / 8192 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartBCDEG1810_natDegree_lt
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
    (n3QuarticColumnBeta810PartBCDEG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n3QuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(245 / 16384 * beta : k)) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (21 / 1024 * beta : k) • (A * C * E)
  + (35 / 2048 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810PartBCDEG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(245 / 16384 * beta) : k), (-(189 / 32768 * beta) : k), (21 / 1024 * beta : k),
      (35 / 2048 * beta : k), (35 / 1024 * beta : k), (21 / 256 * beta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d) :
    (n3QuarticColumnBeta810PartBCDEG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n3QuarticColumnBeta810` on the live set `BCDEG` (2 monomials). -/
def n3QuarticColumnBeta810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 512 * beta : k) • C ^ 3
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnBeta810PartBCDEG3810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnBeta810PartBCDEG3810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 512 * beta : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n3QuarticColumnBeta810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (n3QuarticColumnBeta810PartBCDEG3810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnBeta810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_split_of_live_BCDEG
    (beta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n3QuarticColumnBeta810 beta A B C D E F G =
      n3QuarticColumnBeta810PartBCDEG1810 beta A B C D E F G +
        n3QuarticColumnBeta810PartBCDEG2810 beta A B C D E F G +
        n3QuarticColumnBeta810PartBCDEG3810 beta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnBeta810, n3QuarticColumnBeta810PartBCDEG1810, n3QuarticColumnBeta810PartBCDEG2810, n3QuarticColumnBeta810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (beta : k)
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
    (hd8 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : 2 * E.natDegree < d) :
    (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnBeta810_split_of_live_BCDEG beta A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n3QuarticColumnBeta810PartBCDEG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnBeta810PartBCDEG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n3QuarticColumnBeta810PartBCDEG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnGamma810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree < d)
    (hd5 : D.natDegree + E.natDegree < d) :
    (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnGamma810]
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
/-- Piece 1/2 of `n3QuarticColumnDelta810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 5
  + (15 / 16384 * delta : k) • (A ^ 3 * C)
  - (25 / 8192 * delta : k) • (A ^ 2 * B ^ 2)
  + (55 / 1024 * delta : k) • (A * B * D)
  + (35 / 2048 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnDelta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnDelta810PartBCDEG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 524288 * delta : k), (15 / 16384 * delta : k), (-(25 / 8192 * delta) : k),
      (55 / 1024 * delta : k), (35 / 2048 * delta : k), (45 / 512 * delta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnDelta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d) :
    (n3QuarticColumnDelta810PartBCDEG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnDelta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n3QuarticColumnDelta810` on the live set `BCDEG` (3 monomials). -/
def n3QuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 * delta : k)) • (A * G)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnDelta810PartBCDEG2810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnDelta810PartBCDEG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnDelta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + G.natDegree < d)
    (hd1 : C.natDegree + E.natDegree < d)
    (hd2 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810PartBCDEG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnDelta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_split_of_live_BCDEG
    (delta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n3QuarticColumnDelta810 delta A B C D E F G =
      n3QuarticColumnDelta810PartBCDEG1810 delta A B C D E F G +
        n3QuarticColumnDelta810PartBCDEG2810 delta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnDelta810, n3QuarticColumnDelta810PartBCDEG1810, n3QuarticColumnDelta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + G.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnDelta810_split_of_live_BCDEG delta A B C D E F G hFz]
  exact (natDegree_add_lt810 (n3QuarticColumnDelta810PartBCDEG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnDelta810PartBCDEG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : B.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + D.natDegree < d) :
    (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnEpsilon810]
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
/-- Piece 1/2 of `n3QuarticColumnZeta810` on the live set `BCDEG` (6 monomials). -/
def n3QuarticColumnZeta810PartBCDEG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32768 * zeta : k) • A ^ 4
  + (3 / 1024 * zeta : k) • (A ^ 2 * C)
  + (51 / 2048 * zeta : k) • (A * B ^ 2)
  - (3 / 128 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnZeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnZeta810PartBCDEG1810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 32768 * zeta : k), (3 / 1024 * zeta : k), (51 / 2048 * zeta : k),
      (-(3 / 128 * zeta) : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n3QuarticColumnZeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810PartBCDEG1810_natDegree_lt
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
    (n3QuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnZeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n3QuarticColumnZeta810` on the live set `BCDEG` (1 monomials). -/
def n3QuarticColumnZeta810PartBCDEG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * zeta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticColumnZeta810PartBCDEG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnZeta810PartBCDEG2810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * zeta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n3QuarticColumnZeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : G.natDegree < d) :
    (n3QuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnZeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_split_of_live_BCDEG
    (zeta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n3QuarticColumnZeta810 zeta A B C D E F G =
      n3QuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G +
        n3QuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnZeta810, n3QuarticColumnZeta810PartBCDEG1810, n3QuarticColumnZeta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d)
    (hd6 : G.natDegree < d) :
    (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnZeta810_split_of_live_BCDEG zeta A B C D E F G hFz]
  exact (natDegree_add_lt810 (n3QuarticColumnZeta810PartBCDEG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnZeta810PartBCDEG2810_natDegree_lt zeta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d) :
    (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnEta810]
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
theorem n3QuarticColumnTheta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n3QuarticColumnTheta810]
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
/-- Piece 1/4 of `n4QuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8
  + (315 / 4194304 * l : k) • (A ^ 6 * C)
  - (99 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (45 / 131072 * l : k) • (A ^ 5 * E)
  - (117 / 262144 * l : k) • (A ^ 4 * B * D)
  + (459 / 524288 * l : k) • (A ^ 4 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (495 / 268435456 * l : k), (315 / 4194304 * l : k), (-(99 / 2097152 * l) : k),
      (45 / 131072 * l : k), (-(117 / 262144 * l) : k), (459 / 524288 * l : k)
      ]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnL1810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/4 of `n4QuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 32768 * l : k)) • (A ^ 3 * B ^ 2 * C)
  + (1017 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (9 / 32768 * l : k) • (A ^ 4 * G)
  + (9 / 1024 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (27 / 2048 * l : k) • (A ^ 2 * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 32768 * l) : k), (1017 / 262144 * l : k), (9 / 32768 * l : k),
      (9 / 1024 * l : k), (-(9 / 4096 * l) : k), (-(27 / 2048 * l) : k)
      ]
      [
      [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1], [3, 0, 1, 0, 1, 0, 0],
      [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd2 : 4 * A.natDegree + G.natDegree < d)
    (hd3 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d) :
    (n4QuarticColumnL1810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/4 of `n4QuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(189 / 8192 * l : k)) • (A ^ 2 * B * C * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (27 / 512 * l : k) • (A * B ^ 3 * D)
  - (477 / 8192 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 1024 * l : k) • (A ^ 2 * C * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810PartBCDEG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(189 / 8192 * l) : k), (9 / 16384 * l : k), (-(27 / 512 * l) : k),
      (-(477 / 8192 * l) : k), (-(567 / 16384 * l) : k), (9 / 1024 * l : k)
      ]
      [
      [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0],
      [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1]
      ] := by
  simp only [n4QuarticColumnL1810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 4 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + C.natDegree + G.natDegree < d) :
    (n4QuarticColumnL1810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/4 of `n4QuarticColumnL1810` on the live set `BCDEG` (1 monomials). -/
def n4QuarticColumnL1810PartBCDEG4810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL1810PartBCDEG4810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG4810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL1810PartBCDEG4810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 1024 * l : k)
      ]
      [
      [2, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n4QuarticColumnL1810PartBCDEG4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDEG4810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810PartBCDEG4810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL1810PartBCDEG4810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnL1810 l A B C D E F G =
      n4QuarticColumnL1810PartBCDEG1810 l A B C D E F G +
        n4QuarticColumnL1810PartBCDEG2810 l A B C D E F G +
        n4QuarticColumnL1810PartBCDEG3810 l A B C D E F G +
        n4QuarticColumnL1810PartBCDEG4810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL1810, n4QuarticColumnL1810PartBCDEG1810, n4QuarticColumnL1810PartBCDEG2810, n4QuarticColumnL1810PartBCDEG3810, n4QuarticColumnL1810PartBCDEG4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
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
    (hd18 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnL1810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticColumnL1810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL1810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticColumnL1810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (n4QuarticColumnL1810PartBCDEG4810_natDegree_lt l A B C D E F G hdpos hd18))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n4QuarticColumnL2810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnL2810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 256 * l : k) • (A * B ^ 2 * G)
  + (45 / 256 * l : k) • (A * B * D * E)
  + (27 / 512 * l : k) • (A * C ^ 2 * E)
  + (45 / 512 * l : k) • (A * C * D ^ 2)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 256 * l : k), (45 / 256 * l : k), (27 / 512 * l : k),
      (45 / 512 * l : k), (45 / 256 * l : k), (45 / 512 * l : k)
      ]
      [
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0], [1, 0, 2, 0, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnL2810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (n4QuarticColumnL2810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n4QuarticColumnL2810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnL2810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (189 / 1024 * l : k), (63 / 4096 * l : k), (-(9 / 64 * l) : k),
      (-(9 / 128 * l) : k), (-(9 / 64 * l) : k), (-(9 / 64 * l) : k)
      ]
      [
      [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnL2810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd3 : 2 * C.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + 2 * E.natDegree < d)
    (hd5 : 2 * D.natDegree + E.natDegree < d) :
    (n4QuarticColumnL2810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n4QuarticColumnL2810` on the live set `BCDEG` (1 monomials). -/
def n4QuarticColumnL2810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnL2810PartBCDEG3810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnL2810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 16 * l : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [n4QuarticColumnL2810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnL2810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnL2810 l A B C D E F G =
      n4QuarticColumnL2810PartBCDEG1810 l A B C D E F G +
        n4QuarticColumnL2810PartBCDEG2810 l A B C D E F G +
        n4QuarticColumnL2810PartBCDEG3810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL2810, n4QuarticColumnL2810PartBCDEG1810, n4QuarticColumnL2810PartBCDEG2810, n4QuarticColumnL2810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : 4 * C.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : 2 * C.natDegree + G.natDegree < d)
    (hd10 : C.natDegree + 2 * E.natDegree < d)
    (hd11 : 2 * D.natDegree + E.natDegree < d)
    (hd12 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnL2810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticColumnL2810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL2810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticColumnL2810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n4QuarticColumnBeta1810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnBeta1810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7
  + (35 / 131072 * beta : k) • (A ^ 5 * C)
  - (49 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (21 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 4096 * beta : k) • (A ^ 3 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810PartBCDEG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 2097152 * beta : k), (35 / 131072 * beta : k), (-(49 / 262144 * beta) : k),
      (21 / 16384 * beta : k), (-(7 / 4096 * beta) : k), (21 / 8192 * beta : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + E.natDegree < d)
    (hd4 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCDEG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n4QuarticColumnBeta1810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnBeta1810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 4096 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (427 / 32768 * beta : k) • (A * B ^ 4)
  + (7 / 256 * beta : k) • (A ^ 2 * C * E)
  - (7 / 256 * beta : k) • (A ^ 2 * D ^ 2)
  - (77 / 1024 * beta : k) • (A * B ^ 2 * E)
  - (35 / 256 * beta : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810PartBCDEG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 4096 * beta : k), (427 / 32768 * beta : k), (7 / 256 * beta : k),
      (-(7 / 256 * beta) : k), (-(77 / 1024 * beta) : k), (-(35 / 256 * beta) : k)
      ]
      [
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 4 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCDEG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n4QuarticColumnBeta1810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnBeta1810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 512 * beta : k)) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (21 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnBeta1810PartBCDEG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnBeta1810PartBCDEG3810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 512 * beta) : k), (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k),
      (21 / 128 * beta : k), (7 / 32 * beta : k), (7 / 64 * beta : k)
      ]
      [
      [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnBeta1810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * C.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * C.natDegree + E.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCDEG3810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta1810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_split_of_live_BCDEG
    (beta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnBeta1810 beta A B C D E F G =
      n4QuarticColumnBeta1810PartBCDEG1810 beta A B C D E F G +
        n4QuarticColumnBeta1810PartBCDEG2810 beta A B C D E F G +
        n4QuarticColumnBeta1810PartBCDEG3810 beta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta1810, n4QuarticColumnBeta1810PartBCDEG1810, n4QuarticColumnBeta1810PartBCDEG2810, n4QuarticColumnBeta1810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
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
    (hd15 : A.natDegree + 2 * E.natDegree < d)
    (hd16 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd17 : 2 * C.natDegree + E.natDegree < d) :
    (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnBeta1810_split_of_live_BCDEG beta A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticColumnBeta1810PartBCDEG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnBeta1810PartBCDEG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticColumnBeta1810PartBCDEG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17))

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d) :
    (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnBeta2810]
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
/-- Piece 1/2 of `n4QuarticColumnGamma810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnGamma810PartBCDEG1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  - (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 64 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 32 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnGamma810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnGamma810PartBCDEG1810
    (gamma : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 2048 * gamma : k), (-(3 / 256 * gamma) : k), (-(3 / 256 * gamma) : k),
      (-(9 / 64 * gamma) : k), (-(3 / 32 * gamma) : k), (-(27 / 256 * gamma) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnGamma810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * B.natDegree + C.natDegree < d) :
    (n4QuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnGamma810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnGamma810` on the live set `BCDEG` (4 monomials). -/
def n4QuarticColumnGamma810PartBCDEG2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * gamma : k) • (A * D * E)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnGamma810PartBCDEG2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnGamma810PartBCDEG2810
    (gamma : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * gamma : k), (3 / 8 * gamma : k), (3 / 16 * gamma : k),
      (3 / 16 * gamma : k)
      ]
      [
      [1, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnGamma810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * C.natDegree + D.natDegree < d) :
    (n4QuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnGamma810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_split_of_live_BCDEG
    (gamma : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnGamma810 gamma A B C D E F G =
      n4QuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G +
        n4QuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnGamma810, n4QuarticColumnGamma810PartBCDEG1810, n4QuarticColumnGamma810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : B.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * C.natDegree + D.natDegree < d) :
    (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnGamma810_split_of_live_BCDEG gamma A B C D E F G hFz]
  exact (natDegree_add_lt810 (n4QuarticColumnGamma810PartBCDEG1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnGamma810PartBCDEG2810_natDegree_lt gamma A B C D E F G hdpos hd6 hd7 hd8 hd9))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n4QuarticColumnDelta810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6
  + (15 / 16384 * delta : k) • (A ^ 4 * C)
  - (5 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (25 / 512 * delta : k) • (A ^ 2 * B * D)
  + (5 / 1024 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810PartBCDEG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 262144 * delta : k), (15 / 16384 * delta : k), (-(5 / 16384 * delta) : k),
      (5 / 1024 * delta : k), (-(25 / 512 * delta) : k), (5 / 1024 * delta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + E.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnDelta810PartBCDEG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n4QuarticColumnDelta810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(155 / 1024 * delta : k)) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (15 / 64 * delta : k) • (A * C * E)
  + (25 / 128 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810PartBCDEG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(155 / 1024 * delta) : k), (-(135 / 4096 * delta) : k), (15 / 64 * delta : k),
      (25 / 128 * delta : k), (25 / 128 * delta : k), (15 / 32 * delta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d) :
    (n4QuarticColumnDelta810PartBCDEG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n4QuarticColumnDelta810` on the live set `BCDEG` (2 monomials). -/
def n4QuarticColumnDelta810PartBCDEG3810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • C ^ 3
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnDelta810PartBCDEG3810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartBCDEG3810
    (delta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnDelta810PartBCDEG3810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 64 * delta : k), (-(5 / 16 * delta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [n4QuarticColumnDelta810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810PartBCDEG3810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnDelta810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_split_of_live_BCDEG
    (delta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnDelta810 delta A B C D E F G =
      n4QuarticColumnDelta810PartBCDEG1810 delta A B C D E F G +
        n4QuarticColumnDelta810PartBCDEG2810 delta A B C D E F G +
        n4QuarticColumnDelta810PartBCDEG3810 delta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnDelta810, n4QuarticColumnDelta810PartBCDEG1810, n4QuarticColumnDelta810PartBCDEG2810, n4QuarticColumnDelta810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (delta : k)
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
    (hd8 : A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnDelta810_split_of_live_BCDEG delta A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticColumnDelta810PartBCDEG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnDelta810PartBCDEG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticColumnDelta810PartBCDEG3810_natDegree_lt delta A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnEpsilon810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnEpsilon810PartBCDEG1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 64 * epsilon : k)) • (A ^ 2 * B * C)
  - (1 / 16 * epsilon : k) • (A * B ^ 3)
  + (1 / 4 * epsilon : k) • (A * B * E)
  + (1 / 4 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEpsilon810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEpsilon810PartBCDEG1810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810PartBCDEG1810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 64 * epsilon) : k), (-(1 / 16 * epsilon) : k), (1 / 4 * epsilon : k),
      (1 / 4 * epsilon : k), (7 / 32 * epsilon : k), (1 / 4 * epsilon : k)
      ]
      [
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnEpsilon810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnEpsilon810PartBCDEG1810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEpsilon810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnEpsilon810` on the live set `BCDEG` (1 monomials). -/
def n4QuarticColumnEpsilon810PartBCDEG2810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 2 * epsilon : k)) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEpsilon810PartBCDEG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEpsilon810PartBCDEG2810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810PartBCDEG2810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 2 * epsilon) : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [n4QuarticColumnEpsilon810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : D.natDegree + E.natDegree < d) :
    (n4QuarticColumnEpsilon810PartBCDEG2810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns5_n4QuarticColumnEpsilon810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_split_of_live_BCDEG
    (epsilon : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnEpsilon810 epsilon A B C D E F G =
      n4QuarticColumnEpsilon810PartBCDEG1810 epsilon A B C D E F G +
        n4QuarticColumnEpsilon810PartBCDEG2810 epsilon A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnEpsilon810, n4QuarticColumnEpsilon810PartBCDEG1810, n4QuarticColumnEpsilon810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree < d)
    (hd6 : D.natDegree + E.natDegree < d) :
    (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnEpsilon810_split_of_live_BCDEG epsilon A B C D E F G hFz]
  exact (natDegree_add_lt810 (n4QuarticColumnEpsilon810PartBCDEG1810_natDegree_lt epsilon A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnEpsilon810PartBCDEG2810_natDegree_lt epsilon A B C D E F G hdpos hd6))


end QuarticChamberUnownedSystemColumns5810

end Max11DegreeRoutes
