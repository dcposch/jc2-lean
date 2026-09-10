import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch
import Max11SpeedReflectDegLibScratch

/-! # UnownedSystem load-column bounds, part 6/10

31 of the 403 (carrier, load, live-set) column bounds the
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

section QuarticChamberUnownedSystemColumns6810

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnZeta810` on the live set `BCDEG` (6 monomials). -/
def n4QuarticColumnZeta810PartBCDEG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5
  + (3 / 1024 * zeta : k) • (A ^ 3 * C)
  - (39 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (15 / 64 * zeta : k) • (A * B * D)
  + (9 / 128 * zeta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnZeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnZeta810PartBCDEG1810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 32768 * zeta : k), (3 / 1024 * zeta : k), (-(39 / 2048 * zeta) : k),
      (3 / 128 * zeta : k), (15 / 64 * zeta : k), (9 / 128 * zeta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnZeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnZeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnZeta810` on the live set `BCDEG` (4 monomials). -/
def n4QuarticColumnZeta810PartBCDEG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnZeta810PartBCDEG2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnZeta810PartBCDEG2810
    (zeta : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k),
      (-(3 / 16 * zeta) : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n4QuarticColumnZeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + E.natDegree < d)
    (hd3 : 2 * D.natDegree < d) :
    (n4QuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnZeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_split_of_live_BCDEG
    (zeta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    n4QuarticColumnZeta810 zeta A B C D E F G =
      n4QuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G +
        n4QuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnZeta810, n4QuarticColumnZeta810PartBCDEG1810, n4QuarticColumnZeta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (zeta : k)
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
    (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnZeta810_split_of_live_BCDEG zeta A B C D E F G hFz]
  exact (natDegree_add_lt810 (n4QuarticColumnZeta810PartBCDEG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnZeta810PartBCDEG2810_natDegree_lt zeta A B C D E F G hdpos hd6 hd7 hd8 hd9))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n4QuarticColumnEta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnEta810
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
theorem n4QuarticColumnEta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnEta810]
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
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnTheta810
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
theorem n4QuarticColumnTheta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_n4QuarticColumnTheta810]
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
/-- Piece 1/3 of `nuQuarticColumnL810` on the live set `BCDEG` (6 monomials). -/
def nuQuarticColumnL810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnL810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnL810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnL810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (105 / 4194304 * l : k), (135 / 262144 * l : k), (9 / 4096 * l : k),
      (9 / 8192 * l : k), (9 / 16384 * l : k), (63 / 4096 * l : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnL810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (nuQuarticColumnL810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnL810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `nuQuarticColumnL810` on the live set `BCDEG` (6 monomials). -/
def nuQuarticColumnL810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnL810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnL810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnL810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (315 / 32768 * l : k), (9 / 1024 * l : k), (-(9 / 512 * l) : k),
      (-(63 / 1024 * l) : k), (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnL810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 3 * C.natDegree < d) :
    (nuQuarticColumnL810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnL810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `nuQuarticColumnL810` on the live set `BCDEG` (2 monomials). -/
def nuQuarticColumnL810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * l : k) • (C * G)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnL810PartBCDEG3810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnL810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnL810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [nuQuarticColumnL810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnL810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    nuQuarticColumnL810 l A B C D E F G =
      nuQuarticColumnL810PartBCDEG1810 l A B C D E F G +
        nuQuarticColumnL810PartBCDEG2810 l A B C D E F G +
        nuQuarticColumnL810PartBCDEG3810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnL810, nuQuarticColumnL810PartBCDEG1810, nuQuarticColumnL810PartBCDEG2810, nuQuarticColumnL810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : 2 * A.natDegree + G.natDegree < d)
    (hd8 : A.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * B.natDegree + E.natDegree < d)
    (hd10 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd11 : 3 * C.natDegree < d)
    (hd12 : C.natDegree + G.natDegree < d)
    (hd13 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [nuQuarticColumnL810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (nuQuarticColumnL810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticColumnL810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (nuQuarticColumnL810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def nuQuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnBeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 65536 * beta : k), (7 / 4096 * beta : k), (-(7 / 16384 * beta) : k),
      (7 / 1024 * beta : k), (7 / 256 * beta : k), (63 / 1024 * beta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnBeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d) :
    (nuQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnBeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticColumnBeta810` on the live set `BCDEG` (2 monomials). -/
def nuQuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 64 * beta : k)) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnBeta810PartBCDEG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    nuQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [nuQuarticColumnBeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + E.natDegree < d)
    (hd1 : 2 * D.natDegree < d) :
    (nuQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnBeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_split_of_live_BCDEG
    (beta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    nuQuarticColumnBeta810 beta A B C D E F G =
      nuQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G +
        nuQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnBeta810, nuQuarticColumnBeta810PartBCDEG1810, nuQuarticColumnBeta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BCDEG
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
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : C.natDegree + E.natDegree < d)
    (hd7 : 2 * D.natDegree < d) :
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [nuQuarticColumnBeta810_split_of_live_BCDEG beta A B C D E F G hFz]
  exact (natDegree_add_lt810 (nuQuarticColumnBeta810PartBCDEG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticColumnBeta810PartBCDEG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticColumnGamma810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnGamma810
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
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : B.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + D.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnGamma810]
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
/-- Reflected monomial data for `nuQuarticColumnDelta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnDelta810
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
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnDelta810]
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
/-- Reflected monomial data for `nuQuarticColumnEpsilon810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnEpsilon810
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
theorem nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnEpsilon810]
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
/-- Reflected monomial data for `nuQuarticColumnZeta810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnZeta810
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
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d)
    (hd2 : E.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnZeta810]
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
/-- Reflected monomial data for `nuQuarticColumnEta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnEta810
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
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnEta810]
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
/-- Reflected monomial data for `nuQuarticColumnTheta810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnTheta810
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
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_nuQuarticColumnTheta810]
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
/-- Piece 1/3 of `omicronQuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def omicronQuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (81 / 262144 * l : k) • (A ^ 4 * E)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (81 / 262144 * l : k), (-(9 / 65536 * l) : k), (99 / 131072 * l : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnL1810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCDEG1810_natDegree_lt
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
    (omicronQuarticColumnL1810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `omicronQuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def omicronQuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 131072 * l : k)) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  + (27 / 8192 * l : k) • (A ^ 2 * C * E)
  + (45 / 4096 * l : k) • (A * B ^ 2 * E)
  + (99 / 4096 * l : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 131072 * l) : k), (-(189 / 65536 * l) : k), (9 / 8192 * l : k),
      (27 / 8192 * l : k), (45 / 4096 * l : k), (99 / 4096 * l : k)
      ]
      [
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 0, 1, 0, 1, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnL1810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 4 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + G.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d) :
    (omicronQuarticColumnL1810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `omicronQuarticColumnL1810` on the live set `BCDEG` (5 monomials). -/
def omicronQuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (27 / 1024 * l : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810PartBCDEG3810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 8192 * l : k), (189 / 8192 * l : k), (567 / 16384 * l : k),
      (9 / 512 * l : k), (-(27 / 1024 * l) : k)
      ]
      [
      [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1],
      [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [omicronQuarticColumnL1810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * C.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d) :
    (omicronQuarticColumnL1810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    omicronQuarticColumnL1810 l A B C D E F G =
      omicronQuarticColumnL1810PartBCDEG1810 l A B C D E F G +
        omicronQuarticColumnL1810PartBCDEG2810 l A B C D E F G +
        omicronQuarticColumnL1810PartBCDEG3810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnL1810, omicronQuarticColumnL1810PartBCDEG1810, omicronQuarticColumnL1810PartBCDEG2810, omicronQuarticColumnL1810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_natDegree_lt_of_live_BCDEG
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
    (hd10 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 3 * C.natDegree < d)
    (hd13 : 3 * B.natDegree + D.natDegree < d)
    (hd14 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd15 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd16 : 2 * B.natDegree + G.natDegree < d) :
    (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnL1810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticColumnL1810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnL1810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticColumnL1810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL2810
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
theorem omicronQuarticColumnL2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * D.natDegree < d)
    (hd3 : E.natDegree + G.natDegree < d) :
    (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL2810]
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
/-- Piece 1/3 of `omicronQuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def omicronQuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (7 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnBeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2097152 * beta : k), (49 / 131072 * beta : k), (-(35 / 131072 * beta) : k),
      (7 / 8192 * beta : k), (-(7 / 4096 * beta) : k), (21 / 8192 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnBeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCDEG1810_natDegree_lt
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
    (omicronQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnBeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `omicronQuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def omicronQuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(91 / 8192 * beta : k)) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (7 / 512 * beta : k) • (A * C * E)
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnBeta810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(91 / 8192 * beta) : k), (-(189 / 32768 * beta) : k), (7 / 512 * beta : k),
      (7 / 512 * beta : k), (35 / 1024 * beta : k), (21 / 256 * beta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnBeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCDEG2810_natDegree_lt
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
    (omicronQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnBeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `omicronQuarticColumnBeta810` on the live set `BCDEG` (2 monomials). -/
def omicronQuarticColumnBeta810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 512 * beta : k) • C ^ 3
  - (7 / 128 * beta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnBeta810PartBCDEG3810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnBeta810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnBeta810PartBCDEG3810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 512 * beta : k), (-(7 / 128 * beta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [omicronQuarticColumnBeta810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (omicronQuarticColumnBeta810PartBCDEG3810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnBeta810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_split_of_live_BCDEG
    (beta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    omicronQuarticColumnBeta810 beta A B C D E F G =
      omicronQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G +
        omicronQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G +
        omicronQuarticColumnBeta810PartBCDEG3810 beta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnBeta810, omicronQuarticColumnBeta810PartBCDEG1810, omicronQuarticColumnBeta810PartBCDEG2810, omicronQuarticColumnBeta810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_natDegree_lt_of_live_BCDEG
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
    (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnBeta810_split_of_live_BCDEG beta A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticColumnBeta810PartBCDEG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnBeta810PartBCDEG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticColumnBeta810PartBCDEG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnGamma810` on the live set `BCDEG` (6 monomials). -/
def omicronQuarticColumnGamma810PartBCDEG1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  + (3 / 128 * gamma : k) • (A * B * E)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnGamma810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnGamma810PartBCDEG1810
    (gamma : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 2048 * gamma : k), (-(9 / 1024 * gamma) : k), (3 / 128 * gamma : k),
      (3 / 128 * gamma : k), (9 / 128 * gamma : k), (9 / 128 * gamma : k)
      ]
      [
      [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnGamma810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree < d) :
    (omicronQuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnGamma810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnGamma810` on the live set `BCDEG` (1 monomials). -/
def omicronQuarticColumnGamma810PartBCDEG2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnGamma810PartBCDEG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnGamma810PartBCDEG2810
    (gamma : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [omicronQuarticColumnGamma810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : D.natDegree + E.natDegree < d) :
    (omicronQuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnGamma810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_split_of_live_BCDEG
    (gamma : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    omicronQuarticColumnGamma810 gamma A B C D E F G =
      omicronQuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G +
        omicronQuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnGamma810, omicronQuarticColumnGamma810PartBCDEG1810, omicronQuarticColumnGamma810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (gamma : k)
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
    (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnGamma810_split_of_live_BCDEG gamma A B C D E F G hFz]
  exact (natDegree_add_lt810 (omicronQuarticColumnGamma810PartBCDEG1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnGamma810PartBCDEG2810_natDegree_lt gamma A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnDelta810` on the live set `BCDEG` (6 monomials). -/
def omicronQuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnDelta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnDelta810PartBCDEG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 131072 * delta : k), (5 / 4096 * delta : k), (-(5 / 4096 * delta) : k),
      (5 / 128 * delta : k), (5 / 512 * delta : k), (45 / 512 * delta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnDelta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810PartBCDEG1810_natDegree_lt
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
    (omicronQuarticColumnDelta810PartBCDEG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnDelta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnDelta810` on the live set `BCDEG` (2 monomials). -/
def omicronQuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 32 * delta : k)) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnDelta810PartBCDEG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnDelta810PartBCDEG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnDelta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + E.natDegree < d)
    (hd1 : 2 * D.natDegree < d) :
    (omicronQuarticColumnDelta810PartBCDEG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnDelta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_split_of_live_BCDEG
    (delta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    omicronQuarticColumnDelta810 delta A B C D E F G =
      omicronQuarticColumnDelta810PartBCDEG1810 delta A B C D E F G +
        omicronQuarticColumnDelta810PartBCDEG2810 delta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnDelta810, omicronQuarticColumnDelta810PartBCDEG1810, omicronQuarticColumnDelta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_natDegree_lt_of_live_BCDEG
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
    (hd6 : C.natDegree + E.natDegree < d)
    (hd7 : 2 * D.natDegree < d) :
    (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnDelta810_split_of_live_BCDEG delta A B C D E F G hFz]
  exact (natDegree_add_lt810 (omicronQuarticColumnDelta810PartBCDEG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnDelta810PartBCDEG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnEpsilon810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnEpsilon810
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
theorem omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnEpsilon810]
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
/-- Reflected monomial data for `omicronQuarticColumnZeta810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnZeta810
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
theorem omicronQuarticColumnZeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnZeta810]
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
/-- Reflected monomial data for `omicronQuarticColumnEta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnEta810
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
theorem omicronQuarticColumnEta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + B.natDegree < d)
    (hd1 : A.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree < d) :
    (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnEta810]
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
/-- Reflected monomial data for `omicronQuarticColumnTheta810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnTheta810
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
theorem omicronQuarticColumnTheta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d)
    (hd3 : E.natDegree < d) :
    (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnTheta810]
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
/-- Piece 1/3 of `primitiveQuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL1810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1575 / 268435456 * l : k), (765 / 4194304 * l : k), (-(369 / 4194304 * l) : k),
      (171 / 262144 * l : k), (-(153 / 262144 * l) : k), (855 / 524288 * l : k)
      ]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL1810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCDEG1810_natDegree_lt
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
    (primitiveQuarticColumnL1810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL1810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `primitiveQuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(81 / 131072 * l : k)) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL1810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(81 / 131072 * l) : k), (261 / 262144 * l : k), (45 / 32768 * l : k),
      (99 / 8192 * l : k), (-(9 / 4096 * l) : k), (-(9 / 4096 * l) : k)
      ]
      [
      [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1], [3, 0, 1, 0, 1, 0, 0],
      [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL1810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCDEG2810_natDegree_lt
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
    (primitiveQuarticColumnL1810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL1810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `primitiveQuarticColumnL1810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL1810PartBCDEG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL1810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL1810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 8192 * l : k), (27 / 16384 * l : k), (-(243 / 8192 * l) : k),
      (-(387 / 16384 * l) : k), (-(567 / 16384 * l) : k), (27 / 1024 * l : k)
      ]
      [
      [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0],
      [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1]
      ] := by
  simp only [primitiveQuarticColumnL1810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCDEG3810_natDegree_lt
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
    (primitiveQuarticColumnL1810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL1810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnL1810 l A B C D E F G =
      primitiveQuarticColumnL1810PartBCDEG1810 l A B C D E F G +
        primitiveQuarticColumnL1810PartBCDEG2810 l A B C D E F G +
        primitiveQuarticColumnL1810PartBCDEG3810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnL1810, primitiveQuarticColumnL1810PartBCDEG1810, primitiveQuarticColumnL1810PartBCDEG2810, primitiveQuarticColumnL1810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_natDegree_lt_of_live_BCDEG
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
    (hd17 : 2 * A.natDegree + C.natDegree + G.natDegree < d) :
    (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnL1810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticColumnL1810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnL1810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticColumnL1810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `primitiveQuarticColumnL2810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnL2810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL2810PartBCDEG1810
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810PartBCDEG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 1024 * l : k), (9 / 1024 * l : k), (45 / 512 * l : k),
      (9 / 1024 * l : k), (9 / 256 * l : k), (45 / 256 * l : k)
      ]
      [
      [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 2, 1, 0, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnL2810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnL2810PartBCDEG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL2810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `primitiveQuarticColumnL2810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnL2810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 128 * l : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL2810PartBCDEG2810
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810PartBCDEG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 * l : k), (189 / 1024 * l : k), (63 / 4096 * l : k),
      (9 / 64 * l : k), (-(9 / 64 * l) : k), (-(9 / 128 * l) : k)
      ]
      [
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1],
      [0, 1, 0, 1, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1]
      ] := by
  simp only [primitiveQuarticColumnL2810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d) :
    (primitiveQuarticColumnL2810PartBCDEG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL2810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `primitiveQuarticColumnL2810` on the live set `BCDEG` (3 monomials). -/
def primitiveQuarticColumnL2810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 64 * l : k)) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnL2810PartBCDEG3810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL2810PartBCDEG3810
    (l : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnL2810PartBCDEG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 64 * l) : k), (-(9 / 64 * l) : k), (9 / 16 * l : k)
      ]
      [
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [primitiveQuarticColumnL2810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + 2 * E.natDegree < d)
    (hd1 : 2 * D.natDegree + E.natDegree < d)
    (hd2 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810PartBCDEG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnL2810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_split_of_live_BCDEG
    (l : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnL2810 l A B C D E F G =
      primitiveQuarticColumnL2810PartBCDEG1810 l A B C D E F G +
        primitiveQuarticColumnL2810PartBCDEG2810 l A B C D E F G +
        primitiveQuarticColumnL2810PartBCDEG3810 l A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnL2810, primitiveQuarticColumnL2810PartBCDEG1810, primitiveQuarticColumnL2810PartBCDEG2810, primitiveQuarticColumnL2810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : 4 * C.natDegree < d)
    (hd9 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + 2 * E.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnL2810_split_of_live_BCDEG l A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticColumnL2810PartBCDEG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnL2810PartBCDEG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticColumnL2810PartBCDEG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `primitiveQuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnBeta810PartBCDEG1810
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 1048576 * beta : k), (21 / 32768 * beta : k), (-(119 / 262144 * beta) : k),
      (35 / 16384 * beta : k), (-(7 / 2048 * beta) : k), (21 / 4096 * beta : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCDEG1810_natDegree_lt
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
    (primitiveQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnBeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `primitiveQuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 8192 * beta : k)) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnBeta810PartBCDEG2810
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(21 / 8192 * beta) : k), (119 / 16384 * beta : k), (21 / 512 * beta : k),
      (-(7 / 512 * beta) : k), (-(21 / 512 * beta) : k), (-(7 / 128 * beta) : k)
      ]
      [
      [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0], [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0],
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCDEG2810_natDegree_lt
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
    (primitiveQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnBeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `primitiveQuarticColumnBeta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnBeta810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 128 * beta : k)) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnBeta810PartBCDEG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnBeta810PartBCDEG3810
    (beta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnBeta810PartBCDEG3810 beta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k), (7 / 64 * beta : k),
      (7 / 32 * beta : k), (7 / 64 * beta : k), (7 / 64 * beta : k)
      ]
      [
      [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnBeta810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + D.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : A.natDegree + 2 * E.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * C.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d) :
    (primitiveQuarticColumnBeta810PartBCDEG3810 beta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnBeta810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_split_of_live_BCDEG
    (beta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnBeta810 beta A B C D E F G =
      primitiveQuarticColumnBeta810PartBCDEG1810 beta A B C D E F G +
        primitiveQuarticColumnBeta810PartBCDEG2810 beta A B C D E F G +
        primitiveQuarticColumnBeta810PartBCDEG3810 beta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnBeta810, primitiveQuarticColumnBeta810PartBCDEG1810, primitiveQuarticColumnBeta810PartBCDEG2810, primitiveQuarticColumnBeta810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCDEG
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
    (hd12 : 3 * B.natDegree + D.natDegree < d)
    (hd13 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd14 : A.natDegree + 2 * E.natDegree < d)
    (hd15 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd16 : 2 * C.natDegree + E.natDegree < d)
    (hd17 : C.natDegree + 2 * D.natDegree < d) :
    (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnBeta810_split_of_live_BCDEG beta A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticColumnBeta810PartBCDEG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnBeta810PartBCDEG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticColumnBeta810PartBCDEG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnGamma810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnGamma810PartBCDEG1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnGamma810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnGamma810PartBCDEG1810
    (gamma : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 2048 * gamma : k), (3 / 2048 * gamma : k), (3 / 256 * gamma : k),
      (3 / 256 * gamma : k), (-(9 / 128 * gamma) : k), (-(3 / 128 * gamma) : k)
      ]
      [
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnGamma810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * C.natDegree < d) :
    (primitiveQuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnGamma810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnGamma810` on the live set `BCDEG` (5 monomials). -/
def primitiveQuarticColumnGamma810PartBCDEG2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 256 * gamma : k)) • (B ^ 3 * C)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnGamma810PartBCDEG2810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnGamma810PartBCDEG2810
    (gamma : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 256 * gamma) : k), (3 / 16 * gamma : k), (3 / 8 * gamma : k),
      (3 / 16 * gamma : k), (3 / 16 * gamma : k)
      ]
      [
      [0, 3, 1, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnGamma810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnGamma810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_split_of_live_BCDEG
    (gamma : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnGamma810 gamma A B C D E F G =
      primitiveQuarticColumnGamma810PartBCDEG1810 gamma A B C D E F G +
        primitiveQuarticColumnGamma810PartBCDEG2810 gamma A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnGamma810, primitiveQuarticColumnGamma810PartBCDEG1810, primitiveQuarticColumnGamma810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : B.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnGamma810_split_of_live_BCDEG gamma A B C D E F G hFz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnGamma810PartBCDEG1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnGamma810PartBCDEG2810_natDegree_lt gamma A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `primitiveQuarticColumnDelta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnDelta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnDelta810PartBCDEG1810
    (delta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810PartBCDEG1810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 262144 * delta : k), (35 / 16384 * delta : k), (-(25 / 16384 * delta) : k),
      (5 / 1024 * delta : k), (-(5 / 512 * delta) : k), (15 / 1024 * delta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnDelta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCDEG1810_natDegree_lt
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
    (primitiveQuarticColumnDelta810PartBCDEG1810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnDelta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `primitiveQuarticColumnDelta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(65 / 1024 * delta : k)) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnDelta810PartBCDEG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnDelta810PartBCDEG2810
    (delta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810PartBCDEG2810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(65 / 1024 * delta) : k), (-(135 / 4096 * delta) : k), (5 / 64 * delta : k),
      (5 / 64 * delta : k), (25 / 128 * delta : k), (15 / 32 * delta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnDelta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCDEG2810_natDegree_lt
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
    (primitiveQuarticColumnDelta810PartBCDEG2810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnDelta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `primitiveQuarticColumnDelta810` on the live set `BCDEG` (2 monomials). -/
def primitiveQuarticColumnDelta810PartBCDEG3810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • C ^ 3
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnDelta810PartBCDEG3810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnDelta810PartBCDEG3810
    (delta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnDelta810PartBCDEG3810 delta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 64 * delta : k), (-(5 / 16 * delta) : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnDelta810PartBCDEG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCDEG3810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (primitiveQuarticColumnDelta810PartBCDEG3810 delta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnDelta810PartBCDEG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_split_of_live_BCDEG
    (delta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnDelta810 delta A B C D E F G =
      primitiveQuarticColumnDelta810PartBCDEG1810 delta A B C D E F G +
        primitiveQuarticColumnDelta810PartBCDEG2810 delta A B C D E F G +
        primitiveQuarticColumnDelta810PartBCDEG3810 delta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnDelta810, primitiveQuarticColumnDelta810PartBCDEG1810, primitiveQuarticColumnDelta810PartBCDEG2810, primitiveQuarticColumnDelta810PartBCDEG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCDEG
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
    (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnDelta810_split_of_live_BCDEG delta A B C D E F G hFz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticColumnDelta810PartBCDEG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnDelta810PartBCDEG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticColumnDelta810PartBCDEG3810_natDegree_lt delta A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnEpsilon810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnEpsilon810PartBCDEG1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 256 * epsilon : k)) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEpsilon810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnEpsilon810PartBCDEG1810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEpsilon810PartBCDEG1810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 256 * epsilon) : k), (1 / 64 * epsilon : k), (-(1 / 32 * epsilon) : k),
      (1 / 8 * epsilon : k), (1 / 16 * epsilon : k), (7 / 32 * epsilon : k)
      ]
      [
      [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0],
      [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEpsilon810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnEpsilon810PartBCDEG1810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnEpsilon810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnEpsilon810` on the live set `BCDEG` (2 monomials). -/
def primitiveQuarticColumnEpsilon810PartBCDEG2810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEpsilon810PartBCDEG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnEpsilon810PartBCDEG2810
    (epsilon : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEpsilon810PartBCDEG2810 epsilon A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k)
      ]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEpsilon810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnEpsilon810PartBCDEG2810 epsilon A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnEpsilon810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_split_of_live_BCDEG
    (epsilon : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G =
      primitiveQuarticColumnEpsilon810PartBCDEG1810 epsilon A B C D E F G +
        primitiveQuarticColumnEpsilon810PartBCDEG2810 epsilon A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnEpsilon810, primitiveQuarticColumnEpsilon810PartBCDEG1810, primitiveQuarticColumnEpsilon810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree < d)
    (hd7 : D.natDegree + E.natDegree < d) :
    (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnEpsilon810_split_of_live_BCDEG epsilon A B C D E F G hFz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnEpsilon810PartBCDEG1810_natDegree_lt epsilon A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnEpsilon810PartBCDEG2810_natDegree_lt epsilon A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnZeta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnZeta810PartBCDEG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnZeta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnZeta810PartBCDEG1810
    (zeta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8192 * zeta : k), (3 / 512 * zeta : k), (-(3 / 2048 * zeta) : k),
      (3 / 128 * zeta : k), (3 / 32 * zeta : k), (27 / 128 * zeta : k)
      ]
      [
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnZeta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d) :
    (primitiveQuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnZeta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnZeta810` on the live set `BCDEG` (2 monomials). -/
def primitiveQuarticColumnZeta810PartBCDEG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 8 * zeta : k)) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnZeta810PartBCDEG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnZeta810PartBCDEG2810
    (zeta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 8 * zeta) : k), (-(3 / 16 * zeta) : k)
      ]
      [
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnZeta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + E.natDegree < d)
    (hd1 : 2 * D.natDegree < d) :
    (primitiveQuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnZeta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_split_of_live_BCDEG
    (zeta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnZeta810 zeta A B C D E F G =
      primitiveQuarticColumnZeta810PartBCDEG1810 zeta A B C D E F G +
        primitiveQuarticColumnZeta810PartBCDEG2810 zeta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnZeta810, primitiveQuarticColumnZeta810PartBCDEG1810, primitiveQuarticColumnZeta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : C.natDegree + E.natDegree < d)
    (hd7 : 2 * D.natDegree < d) :
    (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnZeta810_split_of_live_BCDEG zeta A B C D E F G hFz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnZeta810PartBCDEG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnZeta810PartBCDEG2810_natDegree_lt zeta A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnEta810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnEta810
    (eta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnEta810 eta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 512 * eta) : k), (-(1 / 64 * eta) : k), (1 / 32 * eta : k),
      (3 / 64 * eta : k), (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k),
      (-(1 / 4 * eta) : k)
      ]
      [
      [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnEta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree + B.natDegree < d)
    (hd1 : 2 * A.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd3 : 3 * B.natDegree < d)
    (hd4 : B.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnEta810]
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
/-- Piece 1/2 of `primitiveQuarticColumnTheta810` on the live set `BCDEG` (6 monomials). -/
def primitiveQuarticColumnTheta810PartBCDEG1810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnTheta810PartBCDEG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnTheta810PartBCDEG1810
    (theta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnTheta810PartBCDEG1810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 4096 * theta : k), (3 / 128 * theta : k), (1 / 128 * theta : k),
      (1 / 8 * theta : k), (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticColumnTheta810PartBCDEG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810PartBCDEG1810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + D.natDegree < d)
    (hd5 : 2 * C.natDegree < d) :
    (primitiveQuarticColumnTheta810PartBCDEG1810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnTheta810PartBCDEG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnTheta810` on the live set `BCDEG` (1 monomials). -/
def primitiveQuarticColumnTheta810PartBCDEG2810
    (theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticColumnTheta810PartBCDEG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnTheta810PartBCDEG2810
    (theta : k)
    (A B C D E F G : k[X]) :
    primitiveQuarticColumnTheta810PartBCDEG2810 theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 * theta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [primitiveQuarticColumnTheta810PartBCDEG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810PartBCDEG2810_natDegree_lt
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : G.natDegree < d) :
    (primitiveQuarticColumnTheta810PartBCDEG2810 theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_primitiveQuarticColumnTheta810PartBCDEG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_split_of_live_BCDEG
    (theta : k)
    (A B C D E F G : k[X])
    (hFz : F = 0) :
    primitiveQuarticColumnTheta810 theta A B C D E F G =
      primitiveQuarticColumnTheta810PartBCDEG1810 theta A B C D E F G +
        primitiveQuarticColumnTheta810PartBCDEG2810 theta A B C D E F G := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnTheta810, primitiveQuarticColumnTheta810PartBCDEG1810, primitiveQuarticColumnTheta810PartBCDEG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (theta : k)
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
    (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnTheta810_split_of_live_BCDEG theta A B C D E F G hFz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnTheta810PartBCDEG1810_natDegree_lt theta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnTheta810PartBCDEG2810_natDegree_lt theta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `omicronQuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def omicronQuarticColumnL1810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  - (9 / 65536 * l : k) • (A ^ 3 * B * D)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810PartBCDFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810PartBCDFG1810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (135 / 33554432 * l : k), (225 / 2097152 * l : k), (-(171 / 4194304 * l) : k),
      (-(9 / 65536 * l) : k), (99 / 131072 * l : k), (-(45 / 131072 * l) : k)
      ]
      [
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [3, 1, 0, 1, 0, 0, 0],
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnL1810PartBCDFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (omicronQuarticColumnL1810PartBCDFG1810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `omicronQuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def omicronQuarticColumnL1810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(189 / 65536 * l : k)) • (A * B ^ 4)
  + (9 / 8192 * l : k) • (A ^ 3 * G)
  - (9 / 4096 * l : k) • (A ^ 2 * B * F)
  + (99 / 4096 * l : k) • (A * B * C * D)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810PartBCDFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810PartBCDFG2810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(189 / 65536 * l) : k), (9 / 8192 * l : k), (-(9 / 4096 * l) : k),
      (99 / 4096 * l : k), (9 / 8192 * l : k), (189 / 8192 * l : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [1, 1, 1, 1, 0, 0, 0],
      [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0]
      ] := by
  simp only [omicronQuarticColumnL1810PartBCDFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + G.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 3 * C.natDegree < d)
    (hd5 : 3 * B.natDegree + D.natDegree < d) :
    (omicronQuarticColumnL1810PartBCDFG2810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `omicronQuarticColumnL1810` on the live set `BCDFG` (5 monomials). -/
def omicronQuarticColumnL1810PartBCDFG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 512 * l : k) • (A * C * G)
  - (9 / 256 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticColumnL1810PartBCDFG3810` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDFG3810
    (l : k)
    (A B C D E F G : k[X]) :
    omicronQuarticColumnL1810PartBCDFG3810 l A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (567 / 16384 * l : k), (9 / 512 * l : k), (-(9 / 256 * l) : k),
      (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k)
      ]
      [
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [omicronQuarticColumnL1810PartBCDFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCDFG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnL1810PartBCDFG3810 l A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL1810PartBCDFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_split_of_live_BCDFG
    (l : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    omicronQuarticColumnL1810 l A B C D E F G =
      omicronQuarticColumnL1810PartBCDFG1810 l A B C D E F G +
        omicronQuarticColumnL1810PartBCDFG2810 l A B C D E F G +
        omicronQuarticColumnL1810PartBCDFG3810 l A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnL1810, omicronQuarticColumnL1810PartBCDFG1810, omicronQuarticColumnL1810PartBCDFG2810, omicronQuarticColumnL1810PartBCDFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + 4 * B.natDegree < d)
    (hd7 : 3 * A.natDegree + G.natDegree < d)
    (hd8 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + 3 * C.natDegree < d)
    (hd11 : 3 * B.natDegree + D.natDegree < d)
    (hd12 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd13 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd14 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd15 : 2 * B.natDegree + G.natDegree < d)
    (hd16 : B.natDegree + C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnL1810_split_of_live_BCDFG l A B C D E F G hEz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticColumnL1810PartBCDFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnL1810PartBCDFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticColumnL1810PartBCDFG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16))

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemColumns6_omicronQuarticColumnL2810]
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


end QuarticChamberUnownedSystemColumns6810

end Max11DegreeRoutes
