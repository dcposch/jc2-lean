import Grok810ScaleZeroQuarticChamberUnownedTreePackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePackets2Scratch

/-! # UnownedTree load-column bounds, part 3/4

44 of the 197 (carrier, load, live-set) column bounds the
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

section QuarticChamberUnownedTreeColumns3810

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnBeta1810` on the live set `BCFG` (6 monomials). -/
def n4QuarticColumnBeta1810PartBCFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7
  + (35 / 131072 * beta : k) • (A ^ 5 * C)
  - (49 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (21 / 8192 * beta : k) • (A ^ 3 * C ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (427 / 32768 * beta : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnBeta1810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnBeta1810` on the live set `BCFG` (3 monomials). -/
def n4QuarticColumnBeta1810PartBCFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 512 * beta : k)) • (A * C ^ 3)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * C.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnBeta1810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_split_of_live_BCFG
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n4QuarticColumnBeta1810 beta A B C D E F G =
      n4QuarticColumnBeta1810PartBCFG1810 beta A B C D E F G +
        n4QuarticColumnBeta1810PartBCFG2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta1810, n4QuarticColumnBeta1810PartBCFG1810, n4QuarticColumnBeta1810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : A.natDegree + 3 * C.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnBeta1810_split_of_live_BCFG beta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n4QuarticColumnBeta1810PartBCFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnBeta1810PartBCFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * F.natDegree < d) :
    (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d) :
    (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnDelta810` on the live set `BCFG` (6 monomials). -/
def n4QuarticColumnDelta810PartBCFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6
  + (15 / 16384 * delta : k) • (A ^ 4 * C)
  - (5 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (155 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d) :
    (n4QuarticColumnDelta810PartBCFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnDelta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnDelta810` on the live set `BCFG` (2 monomials). -/
def n4QuarticColumnDelta810PartBCFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • (A * B * F)
  + (5 / 64 * delta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd1 : 3 * C.natDegree < d) :
    (n4QuarticColumnDelta810PartBCFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnDelta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_split_of_live_BCFG
    (delta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n4QuarticColumnDelta810 delta A B C D E F G =
      n4QuarticColumnDelta810PartBCFG1810 delta A B C D E F G +
        n4QuarticColumnDelta810PartBCFG2810 delta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnDelta810, n4QuarticColumnDelta810PartBCFG1810, n4QuarticColumnDelta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd7 : 3 * C.natDegree < d) :
    (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnDelta810_split_of_live_BCFG delta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n4QuarticColumnDelta810PartBCFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnDelta810PartBCFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * C.natDegree < d)
    (hd4 : C.natDegree + F.natDegree < d) :
    (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnZeta810` on the live set `BCFG` (6 monomials). -/
def n4QuarticColumnZeta810PartBCFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5
  + (3 / 1024 * zeta : k) • (A ^ 3 * C)
  - (39 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (9 / 128 * zeta : k) • (A * C ^ 2)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d) :
    (n4QuarticColumnZeta810PartBCFG1810 zeta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnZeta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnZeta810` on the live set `BCFG` (1 monomials). -/
def n4QuarticColumnZeta810PartBCFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 8 * zeta : k)) • (B * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + F.natDegree < d) :
    (n4QuarticColumnZeta810PartBCFG2810 zeta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnZeta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_split_of_live_BCFG
    (zeta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n4QuarticColumnZeta810 zeta A B C D E F G =
      n4QuarticColumnZeta810PartBCFG1810 zeta A B C D E F G +
        n4QuarticColumnZeta810PartBCFG2810 zeta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnZeta810, n4QuarticColumnZeta810PartBCFG1810, n4QuarticColumnZeta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnZeta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d) :
    (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnZeta810_split_of_live_BCFG zeta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n4QuarticColumnZeta810PartBCFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnZeta810PartBCFG2810_natDegree_lt zeta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d) :
    (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnTheta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n5QuarticColumnL1810` on the live set `BCFG` (6 monomials). -/
def n5QuarticColumnL1810PartBCFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  - (225 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  + (9 / 65536 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (441 / 262144 * l : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d) :
    (n5QuarticColumnL1810PartBCFG1810 l A B C D E F G).natDegree < d := by
  simp only [n5QuarticColumnL1810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnL1810` on the live set `BCFG` (5 monomials). -/
def n5QuarticColumnL1810PartBCFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 8192 * l : k) • (A ^ 3 * G)
  - (27 / 8192 * l : k) • (A ^ 2 * B * F)
  - (3 / 2048 * l : k) • (A * C ^ 3)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 256 * l : k) • (A * C * G)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + G.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 3 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + G.natDegree < d) :
    (n5QuarticColumnL1810PartBCFG2810 l A B C D E F G).natDegree < d := by
  simp only [n5QuarticColumnL1810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_split_of_live_BCFG
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n5QuarticColumnL1810 l A B C D E F G =
      n5QuarticColumnL1810PartBCFG1810 l A B C D E F G +
        n5QuarticColumnL1810PartBCFG2810 l A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnL1810, n5QuarticColumnL1810PartBCFG1810, n5QuarticColumnL1810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : 3 * A.natDegree + G.natDegree < d)
    (hd7 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 3 * C.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd10 : A.natDegree + C.natDegree + G.natDegree < d) :
    (n5QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnL1810_split_of_live_BCFG l A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n5QuarticColumnL1810PartBCFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnL1810PartBCFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnL2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (n5QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n5QuarticColumnBeta810` on the live set `BCFG` (6 monomials). -/
def n5QuarticColumnBeta810PartBCFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)
  - (7 / 2048 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d) :
    (n5QuarticColumnBeta810PartBCFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n5QuarticColumnBeta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnBeta810` on the live set `BCFG` (3 monomials). -/
def n5QuarticColumnBeta810PartBCFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 512 * beta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 3 * C.natDegree < d) :
    (n5QuarticColumnBeta810PartBCFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n5QuarticColumnBeta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_split_of_live_BCFG
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n5QuarticColumnBeta810 beta A B C D E F G =
      n5QuarticColumnBeta810PartBCFG1810 beta A B C D E F G +
        n5QuarticColumnBeta810PartBCFG2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnBeta810, n5QuarticColumnBeta810PartBCFG1810, n5QuarticColumnBeta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnBeta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : 3 * C.natDegree < d) :
    (n5QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnBeta810_split_of_live_BCFG beta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n5QuarticColumnBeta810PartBCFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnBeta810PartBCFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnGamma810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (n5QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n5QuarticColumnDelta810` on the live set `BCFG` (6 monomials). -/
def n5QuarticColumnDelta810PartBCFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  - (5 / 1024 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d) :
    (n5QuarticColumnDelta810PartBCFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n5QuarticColumnDelta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n5QuarticColumnDelta810` on the live set `BCFG` (1 monomials). -/
def n5QuarticColumnDelta810PartBCFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 * delta : k)) • (B * F)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + F.natDegree < d) :
    (n5QuarticColumnDelta810PartBCFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n5QuarticColumnDelta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_split_of_live_BCFG
    (delta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n5QuarticColumnDelta810 delta A B C D E F G =
      n5QuarticColumnDelta810PartBCFG1810 delta A B C D E F G +
        n5QuarticColumnDelta810PartBCFG2810 delta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnDelta810, n5QuarticColumnDelta810PartBCFG1810, n5QuarticColumnDelta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnDelta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d) :
    (n5QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n5QuarticColumnDelta810_split_of_live_BCFG delta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n5QuarticColumnDelta810PartBCFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n5QuarticColumnDelta810PartBCFG2810_natDegree_lt delta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 3 * B.natDegree < d) :
    (n5QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnZeta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n5QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnEta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (n5QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticColumnTheta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d) :
    (n5QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnL1810` on the live set `BCFG` (6 monomials). -/
def n6QuarticColumnL1810PartBCFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • A ^ 8
  + (105 / 1048576 * l : k) • (A ^ 6 * C)
  - (255 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (585 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (93 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (1425 / 524288 * l : k) • (A ^ 2 * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + 4 * B.natDegree < d) :
    (n6QuarticColumnL1810PartBCFG1810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL1810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnL1810` on the live set `BCFG` (5 monomials). -/
def n6QuarticColumnL1810PartBCFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 32768 * l : k) • (A ^ 4 * G)
  + (11 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  - (765 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (3 / 256 * l : k) • (A ^ 2 * C * G)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + G.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : 2 * A.natDegree + C.natDegree + G.natDegree < d) :
    (n6QuarticColumnL1810PartBCFG2810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL1810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810_split_of_live_BCFG
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n6QuarticColumnL1810 l A B C D E F G =
      n6QuarticColumnL1810PartBCFG1810 l A B C D E F G +
        n6QuarticColumnL1810PartBCFG2810 l A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnL1810, n6QuarticColumnL1810PartBCFG1810, n6QuarticColumnL1810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd6 : 4 * A.natDegree + G.natDegree < d)
    (hd7 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd8 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd9 : 4 * B.natDegree + C.natDegree < d)
    (hd10 : 2 * A.natDegree + C.natDegree + G.natDegree < d) :
    (n6QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnL1810_split_of_live_BCFG l A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n6QuarticColumnL1810PartBCFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnL1810PartBCFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnL2810` on the live set `BCFG` (6 monomials). -/
def n6QuarticColumnL2810PartBCFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 1024 * l : k) • (A * B ^ 2 * G)
  + (21 / 256 * l : k) • (A * B * C * F)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (63 / 4096 * l : k) • C ^ 4
  - (3 / 16 * l : k) • (A * F ^ 2)
  - (9 / 128 * l : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 4 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d) :
    (n6QuarticColumnL2810PartBCFG1810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL2810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnL2810` on the live set `BCFG` (1 monomials). -/
def n6QuarticColumnL2810PartBCFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * G.natDegree < d) :
    (n6QuarticColumnL2810PartBCFG2810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL2810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810_split_of_live_BCFG
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n6QuarticColumnL2810 l A B C D E F G =
      n6QuarticColumnL2810PartBCFG1810 l A B C D E F G +
        n6QuarticColumnL2810PartBCFG2810 l A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnL2810, n6QuarticColumnL2810PartBCFG1810, n6QuarticColumnL2810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 4 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d)
    (hd6 : 2 * G.natDegree < d) :
    (n6QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnL2810_split_of_live_BCFG l A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n6QuarticColumnL2810PartBCFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnL2810PartBCFG2810_natDegree_lt l A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnBeta1810` on the live set `BCFG` (6 monomials). -/
def n6QuarticColumnBeta1810PartBCFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • A ^ 7
  + (35 / 98304 * beta : k) • (A ^ 5 * C)
  - (35 / 131072 * beta : k) • (A ^ 4 * B ^ 2)
  + (7 / 2048 * beta : k) • (A ^ 3 * C ^ 2)
  + (175 / 49152 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (91 / 8192 * beta : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d) :
    (n6QuarticColumnBeta1810PartBCFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnBeta1810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnBeta1810` on the live set `BCFG` (4 monomials). -/
def n6QuarticColumnBeta1810PartBCFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 3072 * beta : k) • (A ^ 2 * B * F)
  - (7 / 768 * beta : k) • (A * C ^ 3)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + 3 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n6QuarticColumnBeta1810PartBCFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnBeta1810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810_split_of_live_BCFG
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n6QuarticColumnBeta1810 beta A B C D E F G =
      n6QuarticColumnBeta1810PartBCFG1810 beta A B C D E F G +
        n6QuarticColumnBeta1810PartBCFG2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnBeta1810, n6QuarticColumnBeta1810PartBCFG1810, n6QuarticColumnBeta1810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd7 : A.natDegree + 3 * C.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd9 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n6QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnBeta1810_split_of_live_BCFG beta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n6QuarticColumnBeta1810PartBCFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnBeta1810PartBCFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * F.natDegree < d) :
    (n6QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnBeta2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnGamma810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d) :
    (n6QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnDelta810` on the live set `BCFG` (6 monomials). -/
def n6QuarticColumnDelta810PartBCFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 6
  + (5 / 4096 * delta : k) • (A ^ 4 * C)
  - (65 / 49152 * delta : k) • (A ^ 3 * B ^ 2)
  + (65 / 6144 * delta : k) • (A ^ 2 * C ^ 2)
  - (125 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d) :
    (n6QuarticColumnDelta810PartBCFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnDelta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnDelta810` on the live set `BCFG` (3 monomials). -/
def n6QuarticColumnDelta810PartBCFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 384 * delta : k)) • (A ^ 2 * G)
  + (5 / 96 * delta : k) • (A * B * F)
  + (5 / 64 * delta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 3 * C.natDegree < d) :
    (n6QuarticColumnDelta810PartBCFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnDelta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810_split_of_live_BCFG
    (delta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n6QuarticColumnDelta810 delta A B C D E F G =
      n6QuarticColumnDelta810PartBCFG1810 delta A B C D E F G +
        n6QuarticColumnDelta810PartBCFG2810 delta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnDelta810, n6QuarticColumnDelta810PartBCFG1810, n6QuarticColumnDelta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : 3 * C.natDegree < d) :
    (n6QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnDelta810_split_of_live_BCFG delta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n6QuarticColumnDelta810PartBCFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnDelta810PartBCFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (n6QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnZeta810` on the live set `BCFG` (6 monomials). -/
def n6QuarticColumnZeta810PartBCFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • A ^ 5
  + (1 / 256 * zeta : k) • (A ^ 3 * C)
  - (11 / 1024 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 64 * zeta : k) • (A * C ^ 2)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (1 / 4 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d) :
    (n6QuarticColumnZeta810PartBCFG1810 zeta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnZeta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnZeta810` on the live set `BCFG` (1 monomials). -/
def n6QuarticColumnZeta810PartBCFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 8 * zeta : k)) • (B * F)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + F.natDegree < d) :
    (n6QuarticColumnZeta810PartBCFG2810 zeta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnZeta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810_split_of_live_BCFG
    (zeta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n6QuarticColumnZeta810 zeta A B C D E F G =
      n6QuarticColumnZeta810PartBCFG1810 zeta A B C D E F G +
        n6QuarticColumnZeta810PartBCFG2810 zeta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnZeta810, n6QuarticColumnZeta810PartBCFG1810, n6QuarticColumnZeta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d) :
    (n6QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnZeta810_split_of_live_BCFG zeta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n6QuarticColumnZeta810PartBCFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnZeta810PartBCFG2810_natDegree_lt zeta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnEta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d) :
    (n6QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnTheta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n6QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n7QuarticColumnL1810` on the live set `BCFG` (6 monomials). -/
def n7QuarticColumnL1810PartBCFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (6435 / 268435456 * l : k) • A ^ 8
  + (315 / 524288 * l : k) • (A ^ 6 * C)
  - (315 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (1485 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (63 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  - (45 / 524288 * l : k) • (A ^ 2 * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + 4 * B.natDegree < d) :
    (n7QuarticColumnL1810PartBCFG1810 l A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnL1810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n7QuarticColumnL1810` on the live set `BCFG` (6 monomials). -/
def n7QuarticColumnL1810PartBCFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • (A ^ 4 * G)
  - (45 / 8192 * l : k) • (A ^ 3 * B * F)
  - (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  + (45 / 4096 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 128 * l : k) • (A ^ 2 * C * G)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + G.natDegree < d)
    (hd1 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 4 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + C.natDegree + G.natDegree < d) :
    (n7QuarticColumnL1810PartBCFG2810 l A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnL1810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_split_of_live_BCFG
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n7QuarticColumnL1810 l A B C D E F G =
      n7QuarticColumnL1810PartBCFG1810 l A B C D E F G +
        n7QuarticColumnL1810PartBCFG2810 l A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnL1810, n7QuarticColumnL1810PartBCFG1810, n7QuarticColumnL1810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd6 : 4 * A.natDegree + G.natDegree < d)
    (hd7 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd9 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd10 : 4 * B.natDegree + C.natDegree < d)
    (hd11 : 2 * A.natDegree + C.natDegree + G.natDegree < d) :
    (n7QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n7QuarticColumnL1810_split_of_live_BCFG l A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n7QuarticColumnL1810PartBCFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnL1810PartBCFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n7QuarticColumnL2810` on the live set `BCFG` (6 monomials). -/
def n7QuarticColumnL2810PartBCFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 512 * l : k)) • (A * B ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * C * F)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (63 / 4096 * l : k) • C ^ 4
  - (9 / 128 * l : k) • (A * F ^ 2)
  - (9 / 128 * l : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 4 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d) :
    (n7QuarticColumnL2810PartBCFG1810 l A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnL2810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n7QuarticColumnL2810` on the live set `BCFG` (1 monomials). -/
def n7QuarticColumnL2810PartBCFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * G.natDegree < d) :
    (n7QuarticColumnL2810PartBCFG2810 l A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnL2810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_split_of_live_BCFG
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n7QuarticColumnL2810 l A B C D E F G =
      n7QuarticColumnL2810PartBCFG1810 l A B C D E F G +
        n7QuarticColumnL2810PartBCFG2810 l A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnL2810, n7QuarticColumnL2810PartBCFG1810, n7QuarticColumnL2810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnL2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 4 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d)
    (hd6 : 2 * G.natDegree < d) :
    (n7QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n7QuarticColumnL2810_split_of_live_BCFG l A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n7QuarticColumnL2810PartBCFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnL2810PartBCFG2810_natDegree_lt l A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n7QuarticColumnBeta1810` on the live set `BCFG` (6 monomials). -/
def n7QuarticColumnBeta1810PartBCFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (429 / 4194304 * beta : k) • A ^ 7
  + (35 / 16384 * beta : k) • (A ^ 5 * C)
  - (35 / 65536 * beta : k) • (A ^ 4 * B ^ 2)
  + (91 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  - (35 / 16384 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (49 / 32768 * beta : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d) :
    (n7QuarticColumnBeta1810PartBCFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnBeta1810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n7QuarticColumnBeta1810` on the live set `BCFG` (5 monomials). -/
def n7QuarticColumnBeta1810PartBCFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 1024 * beta : k) • (A ^ 3 * G)
  - (21 / 1024 * beta : k) • (A ^ 2 * B * F)
  + (7 / 512 * beta : k) • (A * C ^ 3)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + G.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 3 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n7QuarticColumnBeta1810PartBCFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnBeta1810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_split_of_live_BCFG
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n7QuarticColumnBeta1810 beta A B C D E F G =
      n7QuarticColumnBeta1810PartBCFG1810 beta A B C D E F G +
        n7QuarticColumnBeta1810PartBCFG2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnBeta1810, n7QuarticColumnBeta1810PartBCFG1810, n7QuarticColumnBeta1810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : 3 * A.natDegree + G.natDegree < d)
    (hd7 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 3 * C.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd10 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n7QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n7QuarticColumnBeta1810_split_of_live_BCFG beta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n7QuarticColumnBeta1810PartBCFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnBeta1810PartBCFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnBeta2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * F.natDegree < d) :
    (n7QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnBeta2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnGamma810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d) :
    (n7QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n7QuarticColumnDelta810` on the live set `BCFG` (6 monomials). -/
def n7QuarticColumnDelta810PartBCFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 524288 * delta : k) • A ^ 6
  + (15 / 2048 * delta : k) • (A ^ 4 * C)
  - (15 / 8192 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 2048 * delta : k) • (A ^ 2 * C ^ 2)
  + (25 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d) :
    (n7QuarticColumnDelta810PartBCFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnDelta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n7QuarticColumnDelta810` on the live set `BCFG` (3 monomials). -/
def n7QuarticColumnDelta810PartBCFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 128 * delta : k) • (A ^ 2 * G)
  - (5 / 64 * delta : k) • (A * B * F)
  + (5 / 64 * delta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 3 * C.natDegree < d) :
    (n7QuarticColumnDelta810PartBCFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnDelta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810_split_of_live_BCFG
    (delta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n7QuarticColumnDelta810 delta A B C D E F G =
      n7QuarticColumnDelta810PartBCFG1810 delta A B C D E F G +
        n7QuarticColumnDelta810PartBCFG2810 delta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnDelta810, n7QuarticColumnDelta810PartBCFG1810, n7QuarticColumnDelta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnDelta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : 3 * C.natDegree < d) :
    (n7QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n7QuarticColumnDelta810_split_of_live_BCFG delta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n7QuarticColumnDelta810PartBCFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnDelta810PartBCFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (n7QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n7QuarticColumnZeta810` on the live set `BCFG` (6 monomials). -/
def n7QuarticColumnZeta810PartBCFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 32768 * zeta : k) • A ^ 5
  + (3 / 128 * zeta : k) • (A ^ 3 * C)
  - (3 / 512 * zeta : k) • (A ^ 2 * B ^ 2)
  - (9 / 128 * zeta : k) • (A * C ^ 2)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (3 / 8 * zeta : k) • (A * G)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d) :
    (n7QuarticColumnZeta810PartBCFG1810 zeta A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnZeta810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n7QuarticColumnZeta810` on the live set `BCFG` (1 monomials). -/
def n7QuarticColumnZeta810PartBCFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 8 * zeta : k)) • (B * F)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + F.natDegree < d) :
    (n7QuarticColumnZeta810PartBCFG2810 zeta A B C D E F G).natDegree < d := by
  simp only [n7QuarticColumnZeta810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810_split_of_live_BCFG
    (zeta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    n7QuarticColumnZeta810 zeta A B C D E F G =
      n7QuarticColumnZeta810PartBCFG1810 zeta A B C D E F G +
        n7QuarticColumnZeta810PartBCFG2810 zeta A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnZeta810, n7QuarticColumnZeta810PartBCFG1810, n7QuarticColumnZeta810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnZeta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d) :
    (n7QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n7QuarticColumnZeta810_split_of_live_BCFG zeta A B C D E F G hDz hEz]
  exact natDegree_add_lt810 (n7QuarticColumnZeta810PartBCFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n7QuarticColumnZeta810PartBCFG2810_natDegree_lt zeta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnEta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d) :
    (n7QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticColumnTheta810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n7QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnEta810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0) :
    (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + E.natDegree < d)
    (hd2 : 4 * A.natDegree + G.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : A.natDegree + 2 * F.natDegree < d)
    (hd1 : 2 * D.natDegree + E.natDegree < d)
    (hd2 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + 2 * E.natDegree < d) :
    (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta2810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 2 * F.natDegree < d) :
    (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : E.natDegree + F.natDegree < d) :
    (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega


end QuarticChamberUnownedTreeColumns3810

end Max11DegreeRoutes
