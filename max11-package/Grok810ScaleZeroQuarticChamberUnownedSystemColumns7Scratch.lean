import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch

/-! # UnownedSystem load-column bounds, part 7/10

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

section QuarticChamberUnownedSystemColumns7810

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnBeta810` on the live set `BCDFG` (6 monomials). -/
def omicronQuarticColumnBeta810PartBCDFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  - (7 / 4096 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (omicronQuarticColumnBeta810PartBCDFG1810 beta A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnBeta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnBeta810` on the live set `BCDFG` (5 monomials). -/
def omicronQuarticColumnBeta810PartBCDFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(189 / 32768 * beta : k)) • B ^ 4
  + (7 / 512 * beta : k) • (A * D ^ 2)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * C.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (omicronQuarticColumnBeta810PartBCDFG2810 beta A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnBeta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_split_of_live_BCDFG
    (beta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    omicronQuarticColumnBeta810 beta A B C D E F G =
      omicronQuarticColumnBeta810PartBCDFG1810 beta A B C D E F G +
        omicronQuarticColumnBeta810PartBCDFG2810 beta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnBeta810, omicronQuarticColumnBeta810PartBCDFG1810, omicronQuarticColumnBeta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : A.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd9 : 3 * C.natDegree < d)
    (hd10 : D.natDegree + F.natDegree < d) :
    (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnBeta810_split_of_live_BCDFG beta A B C D E F G hEz]
  exact (natDegree_add_lt810 (omicronQuarticColumnBeta810PartBCDFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnBeta810PartBCDFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnGamma810` on the live set `BCDFG` (6 monomials). -/
def omicronQuarticColumnGamma810PartBCDFG1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 2 * B * C)
  - (9 / 1024 * gamma : k) • (A * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 2 * F)
  + (3 / 128 * gamma : k) • (A * C * D)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree < d) :
    (omicronQuarticColumnGamma810PartBCDFG1810 gamma A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnGamma810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnGamma810` on the live set `BCDFG` (1 monomials). -/
def omicronQuarticColumnGamma810PartBCDFG2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 32 * gamma : k)) • (C * F)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnGamma810PartBCDFG2810 gamma A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnGamma810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_split_of_live_BCDFG
    (gamma : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    omicronQuarticColumnGamma810 gamma A B C D E F G =
      omicronQuarticColumnGamma810PartBCDFG1810 gamma A B C D E F G +
        omicronQuarticColumnGamma810PartBCDFG2810 gamma A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnGamma810, omicronQuarticColumnGamma810PartBCDFG1810, omicronQuarticColumnGamma810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree < d)
    (hd6 : C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnGamma810_split_of_live_BCDFG gamma A B C D E F G hEz]
  exact (natDegree_add_lt810 (omicronQuarticColumnGamma810PartBCDFG1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnGamma810PartBCDFG2810_natDegree_lt gamma A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnDelta810` on the live set `BCDFG` (6 monomials). -/
def omicronQuarticColumnDelta810PartBCDFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 131072 * delta : k) • A ^ 5
  + (5 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 4096 * delta : k) • (A ^ 2 * B ^ 2)
  + (5 / 128 * delta : k) • (A * B * D)
  + (5 / 512 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810PartBCDFG1810_natDegree_lt
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
    (omicronQuarticColumnDelta810PartBCDFG1810 delta A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnDelta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnDelta810` on the live set `BCDFG` (2 monomials). -/
def omicronQuarticColumnDelta810PartBCDFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 * delta : k)) • (B * F)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + F.natDegree < d)
    (hd1 : 2 * D.natDegree < d) :
    (omicronQuarticColumnDelta810PartBCDFG2810 delta A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnDelta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_split_of_live_BCDFG
    (delta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    omicronQuarticColumnDelta810 delta A B C D E F G =
      omicronQuarticColumnDelta810PartBCDFG1810 delta A B C D E F G +
        omicronQuarticColumnDelta810PartBCDFG2810 delta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnDelta810, omicronQuarticColumnDelta810PartBCDFG1810, omicronQuarticColumnDelta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : 2 * D.natDegree < d) :
    (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnDelta810_split_of_live_BCDFG delta A B C D E F G hEz]
  exact (natDegree_add_lt810 (omicronQuarticColumnDelta810PartBCDFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnDelta810PartBCDFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : A.natDegree + F.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnZeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + B.natDegree < d)
    (hd1 : A.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree < d)
    (hd3 : F.natDegree < d) :
    (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnTheta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d) :
    (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `primitiveQuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnL1810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (primitiveQuarticColumnL1810PartBCDFG1810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL1810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `primitiveQuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnL1810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : 4 * A.natDegree + G.natDegree < d)
    (hd2 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + 3 * C.natDegree < d) :
    (primitiveQuarticColumnL1810PartBCDFG2810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL1810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `primitiveQuarticColumnL1810` on the live set `BCDFG` (5 monomials). -/
def primitiveQuarticColumnL1810PartBCDFG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(243 / 8192 * l : k)) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCDFG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + C.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd4 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnL1810PartBCDFG3810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL1810PartBCDFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_split_of_live_BCDFG
    (l : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnL1810 l A B C D E F G =
      primitiveQuarticColumnL1810PartBCDFG1810 l A B C D E F G +
        primitiveQuarticColumnL1810PartBCDFG2810 l A B C D E F G +
        primitiveQuarticColumnL1810PartBCDFG3810 l A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnL1810, primitiveQuarticColumnL1810PartBCDFG1810, primitiveQuarticColumnL1810PartBCDFG2810, primitiveQuarticColumnL1810PartBCDFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd7 : 4 * A.natDegree + G.natDegree < d)
    (hd8 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd11 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd12 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd13 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd14 : 4 * B.natDegree + C.natDegree < d)
    (hd15 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd16 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnL1810_split_of_live_BCDFG l A B C D E F G hEz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticColumnL1810PartBCDFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnL1810PartBCDFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticColumnL1810PartBCDFG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnL2810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnL2810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnL2810PartBCDFG1810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL2810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnL2810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnL2810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 4096 * l : k) • C ^ 4
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * C.natDegree < d)
    (hd1 : A.natDegree + 2 * F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd3 : 2 * C.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810PartBCDFG2810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL2810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_split_of_live_BCDFG
    (l : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnL2810 l A B C D E F G =
      primitiveQuarticColumnL2810PartBCDFG1810 l A B C D E F G +
        primitiveQuarticColumnL2810PartBCDFG2810 l A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnL2810, primitiveQuarticColumnL2810PartBCDFG1810, primitiveQuarticColumnL2810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : 4 * C.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : 2 * C.natDegree + G.natDegree < d)
    (hd10 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd11 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnL2810_split_of_live_BCDFG l A B C D E F G hEz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnL2810PartBCDFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnL2810PartBCDFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `primitiveQuarticColumnBeta810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnBeta810PartBCDFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (primitiveQuarticColumnBeta810PartBCDFG1810 beta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnBeta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `primitiveQuarticColumnBeta810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnBeta810PartBCDFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (119 / 16384 * beta : k) • (A * B ^ 4)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnBeta810PartBCDFG2810 beta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnBeta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `primitiveQuarticColumnBeta810` on the live set `BCDFG` (2 monomials). -/
def primitiveQuarticColumnBeta810PartBCDFG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCDFG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (primitiveQuarticColumnBeta810PartBCDFG3810 beta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnBeta810PartBCDFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_split_of_live_BCDFG
    (beta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnBeta810 beta A B C D E F G =
      primitiveQuarticColumnBeta810PartBCDFG1810 beta A B C D E F G +
        primitiveQuarticColumnBeta810PartBCDFG2810 beta A B C D E F G +
        primitiveQuarticColumnBeta810PartBCDFG3810 beta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnBeta810, primitiveQuarticColumnBeta810PartBCDFG1810, primitiveQuarticColumnBeta810PartBCDFG2810, primitiveQuarticColumnBeta810PartBCDFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (beta : k)
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
    (hd7 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd9 : 3 * B.natDegree + D.natDegree < d)
    (hd10 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + 2 * D.natDegree < d)
    (hd13 : 2 * F.natDegree < d) :
    (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnBeta810_split_of_live_BCDFG beta A B C D E F G hEz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticColumnBeta810PartBCDFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnBeta810PartBCDFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticColumnBeta810PartBCDFG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnGamma810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnGamma810PartBCDFG1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * C.natDegree < d) :
    (primitiveQuarticColumnGamma810PartBCDFG1810 gamma A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnGamma810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnGamma810` on the live set `BCDFG` (5 monomials). -/
def primitiveQuarticColumnGamma810PartBCDFG2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 256 * gamma : k)) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnGamma810PartBCDFG2810 gamma A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnGamma810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_split_of_live_BCDFG
    (gamma : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnGamma810 gamma A B C D E F G =
      primitiveQuarticColumnGamma810PartBCDFG1810 gamma A B C D E F G +
        primitiveQuarticColumnGamma810PartBCDFG2810 gamma A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnGamma810, primitiveQuarticColumnGamma810PartBCDFG1810, primitiveQuarticColumnGamma810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * B.natDegree + C.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + F.natDegree < d)
    (hd9 : B.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnGamma810_split_of_live_BCDFG gamma A B C D E F G hEz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnGamma810PartBCDFG1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnGamma810PartBCDFG2810_natDegree_lt gamma A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnDelta810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnDelta810PartBCDFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (primitiveQuarticColumnDelta810PartBCDFG1810 delta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnDelta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnDelta810` on the live set `BCDFG` (5 monomials). -/
def primitiveQuarticColumnDelta810PartBCDFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(135 / 4096 * delta : k)) • B ^ 4
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * C.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnDelta810PartBCDFG2810 delta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnDelta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_split_of_live_BCDFG
    (delta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnDelta810 delta A B C D E F G =
      primitiveQuarticColumnDelta810PartBCDFG1810 delta A B C D E F G +
        primitiveQuarticColumnDelta810PartBCDFG2810 delta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnDelta810, primitiveQuarticColumnDelta810PartBCDFG1810, primitiveQuarticColumnDelta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : A.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd9 : 3 * C.natDegree < d)
    (hd10 : D.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnDelta810_split_of_live_BCDFG delta A B C D E F G hEz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnDelta810PartBCDFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnDelta810PartBCDFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnEpsilon810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnEpsilon810PartBCDFG1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 256 * epsilon : k)) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnEpsilon810PartBCDFG1810 epsilon A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnEpsilon810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnEpsilon810` on the live set `BCDFG` (2 monomials). -/
def primitiveQuarticColumnEpsilon810PartBCDFG2810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * C.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnEpsilon810PartBCDFG2810 epsilon A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnEpsilon810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_split_of_live_BCDFG
    (epsilon : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnEpsilon810 epsilon A B C D E F G =
      primitiveQuarticColumnEpsilon810PartBCDFG1810 epsilon A B C D E F G +
        primitiveQuarticColumnEpsilon810PartBCDFG2810 epsilon A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnEpsilon810, primitiveQuarticColumnEpsilon810PartBCDFG1810, primitiveQuarticColumnEpsilon810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree < d)
    (hd7 : C.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnEpsilon810_split_of_live_BCDFG epsilon A B C D E F G hEz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnEpsilon810PartBCDFG1810_natDegree_lt epsilon A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnEpsilon810PartBCDFG2810_natDegree_lt epsilon A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnZeta810` on the live set `BCDFG` (6 monomials). -/
def primitiveQuarticColumnZeta810PartBCDFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : B.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnZeta810PartBCDFG1810 zeta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnZeta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnZeta810` on the live set `BCDFG` (1 monomials). -/
def primitiveQuarticColumnZeta810PartBCDFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * zeta : k)) • D ^ 2

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree < d) :
    (primitiveQuarticColumnZeta810PartBCDFG2810 zeta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnZeta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_split_of_live_BCDFG
    (zeta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    primitiveQuarticColumnZeta810 zeta A B C D E F G =
      primitiveQuarticColumnZeta810PartBCDFG1810 zeta A B C D E F G +
        primitiveQuarticColumnZeta810PartBCDFG2810 zeta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnZeta810, primitiveQuarticColumnZeta810PartBCDFG1810, primitiveQuarticColumnZeta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : B.natDegree + F.natDegree < d)
    (hd6 : 2 * D.natDegree < d) :
    (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnZeta810_split_of_live_BCDFG zeta A B C D E F G hEz]
  exact (natDegree_add_lt810 (primitiveQuarticColumnZeta810PartBCDFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnZeta810PartBCDFG2810_natDegree_lt zeta A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree + B.natDegree < d)
    (hd1 : 2 * A.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd3 : 3 * B.natDegree < d)
    (hd4 : A.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + D.natDegree < d) :
    (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n3QuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def n3QuarticColumnL1810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (165 / 67108864 * l : k) • A ^ 7
  + (315 / 4194304 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  - (27 / 131072 * l : k) • (A ^ 3 * B * D)
  + (189 / 262144 * l : k) • (A ^ 3 * C ^ 2)
  - (171 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDFG1810_natDegree_lt
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
    (n3QuarticColumnL1810PartBCDFG1810 l A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnL1810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n3QuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def n3QuarticColumnL1810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1827 / 524288 * l : k)) • (A * B ^ 4)
  + (9 / 16384 * l : k) • (A ^ 3 * G)
  + (9 / 8192 * l : k) • (A ^ 2 * D ^ 2)
  + (261 / 8192 * l : k) • (A * B * C * D)
  + (39 / 16384 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + G.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 3 * C.natDegree < d)
    (hd5 : 3 * B.natDegree + D.natDegree < d) :
    (n3QuarticColumnL1810PartBCDFG2810 l A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnL1810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n3QuarticColumnL1810` on the live set `BCDFG` (4 monomials). -/
def n3QuarticColumnL1810PartBCDFG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 1024 * l : k) • (A * C * G)
  - (45 / 1024 * l : k) • (A * D * F)
  - (27 / 1024 * l : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810PartBCDFG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d) :
    (n3QuarticColumnL1810PartBCDFG3810 l A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnL1810PartBCDFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_split_of_live_BCDFG
    (l : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n3QuarticColumnL1810 l A B C D E F G =
      n3QuarticColumnL1810PartBCDFG1810 l A B C D E F G +
        n3QuarticColumnL1810PartBCDFG2810 l A B C D E F G +
        n3QuarticColumnL1810PartBCDFG3810 l A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnL1810, n3QuarticColumnL1810PartBCDFG1810, n3QuarticColumnL1810PartBCDFG2810, n3QuarticColumnL1810PartBCDFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL1810_natDegree_lt_of_live_BCDFG
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
    (hd8 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + 3 * C.natDegree < d)
    (hd11 : 3 * B.natDegree + D.natDegree < d)
    (hd12 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd13 : A.natDegree + C.natDegree + G.natDegree < d)
    (hd14 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd15 : 2 * B.natDegree + G.natDegree < d) :
    (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnL1810_split_of_live_BCDFG l A B C D E F G hEz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n3QuarticColumnL1810PartBCDFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnL1810PartBCDFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n3QuarticColumnL1810PartBCDFG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15))

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnL2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n3QuarticColumnBeta810` on the live set `BCDFG` (6 monomials). -/
def n3QuarticColumnBeta810PartBCDFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2097152 * beta : k) • A ^ 6
  + (35 / 131072 * beta : k) • (A ^ 4 * C)
  - (63 / 262144 * beta : k) • (A ^ 3 * B ^ 2)
  - (7 / 2048 * beta : k) • (A ^ 2 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (245 / 16384 * beta : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (n3QuarticColumnBeta810PartBCDFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnBeta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n3QuarticColumnBeta810` on the live set `BCDFG` (6 monomials). -/
def n3QuarticColumnBeta810PartBCDFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(189 / 32768 * beta : k)) • B ^ 4
  + (7 / 1024 * beta : k) • (A * B * F)
  + (35 / 2048 * beta : k) • (A * D ^ 2)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 3 * C.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (n3QuarticColumnBeta810PartBCDFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnBeta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_split_of_live_BCDFG
    (beta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n3QuarticColumnBeta810 beta A B C D E F G =
      n3QuarticColumnBeta810PartBCDFG1810 beta A B C D E F G +
        n3QuarticColumnBeta810PartBCDFG2810 beta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnBeta810, n3QuarticColumnBeta810PartBCDFG1810, n3QuarticColumnBeta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnBeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : 3 * C.natDegree < d)
    (hd11 : D.natDegree + F.natDegree < d) :
    (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnBeta810_split_of_live_BCDFG beta A B C D E F G hEz]
  exact (natDegree_add_lt810 (n3QuarticColumnBeta810PartBCDFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnBeta810PartBCDFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnGamma810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + D.natDegree < d)
    (hd3 : B.natDegree + 2 * C.natDegree < d)
    (hd4 : C.natDegree + F.natDegree < d) :
    (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n3QuarticColumnDelta810` on the live set `BCDFG` (6 monomials). -/
def n3QuarticColumnDelta810PartBCDFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 5
  + (15 / 16384 * delta : k) • (A ^ 3 * C)
  - (25 / 8192 * delta : k) • (A ^ 2 * B ^ 2)
  + (55 / 1024 * delta : k) • (A * B * D)
  + (35 / 2048 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810PartBCDFG1810_natDegree_lt
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
    (n3QuarticColumnDelta810PartBCDFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnDelta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n3QuarticColumnDelta810` on the live set `BCDFG` (3 monomials). -/
def n3QuarticColumnDelta810PartBCDFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 * delta : k)) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + F.natDegree < d)
    (hd2 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810PartBCDFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n3QuarticColumnDelta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_split_of_live_BCDFG
    (delta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n3QuarticColumnDelta810 delta A B C D E F G =
      n3QuarticColumnDelta810PartBCDFG1810 delta A B C D E F G +
        n3QuarticColumnDelta810PartBCDFG2810 delta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnDelta810, n3QuarticColumnDelta810PartBCDFG1810, n3QuarticColumnDelta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnDelta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + F.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n3QuarticColumnDelta810_split_of_live_BCDFG delta A B C D E F G hEz]
  exact (natDegree_add_lt810 (n3QuarticColumnDelta810PartBCDFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticColumnDelta810PartBCDFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + D.natDegree < d) :
    (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnZeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnTheta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d) :
    (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n4QuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnL1810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8
  + (315 / 4194304 * l : k) • (A ^ 6 * C)
  - (99 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  - (117 / 262144 * l : k) • (A ^ 4 * B * D)
  + (459 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (9 / 32768 * l : k) • (A ^ 3 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (n4QuarticColumnL1810PartBCDFG1810 l A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnL1810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n4QuarticColumnL1810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnL1810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1017 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (9 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (189 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (27 / 512 * l : k) • (A * B ^ 3 * D)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : 4 * A.natDegree + G.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd5 : A.natDegree + 3 * B.natDegree + D.natDegree < d) :
    (n4QuarticColumnL1810PartBCDFG2810 l A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnL1810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n4QuarticColumnL1810` on the live set `BCDFG` (4 monomials). -/
def n4QuarticColumnL1810PartBCDFG3810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(477 / 8192 * l : k)) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 1024 * l : k) • (A ^ 2 * C * G)
  + (9 / 512 * l : k) • (A ^ 2 * D * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810PartBCDFG3810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd3 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (n4QuarticColumnL1810PartBCDFG3810 l A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnL1810PartBCDFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_split_of_live_BCDFG
    (l : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n4QuarticColumnL1810 l A B C D E F G =
      n4QuarticColumnL1810PartBCDFG1810 l A B C D E F G +
        n4QuarticColumnL1810PartBCDFG2810 l A B C D E F G +
        n4QuarticColumnL1810PartBCDFG3810 l A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL1810, n4QuarticColumnL1810PartBCDFG1810, n4QuarticColumnL1810PartBCDFG2810, n4QuarticColumnL1810PartBCDFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd7 : 4 * A.natDegree + G.natDegree < d)
    (hd8 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd11 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd13 : 4 * B.natDegree + C.natDegree < d)
    (hd14 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd15 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnL1810_split_of_live_BCDFG l A B C D E F G hEz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticColumnL1810PartBCDFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL1810PartBCDFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticColumnL1810PartBCDFG3810_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnL2810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnL2810PartBCDFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 256 * l : k) • (A * B ^ 2 * G)
  + (27 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (n4QuarticColumnL2810PartBCDFG1810 l A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnL2810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnL2810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnL2810PartBCDFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 4096 * l : k) • C ^ 4
  - (27 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * C.natDegree < d)
    (hd1 : A.natDegree + 2 * F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd3 : 2 * C.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810PartBCDFG2810 l A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnL2810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_split_of_live_BCDFG
    (l : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n4QuarticColumnL2810 l A B C D E F G =
      n4QuarticColumnL2810PartBCDFG1810 l A B C D E F G +
        n4QuarticColumnL2810PartBCDFG2810 l A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnL2810, n4QuarticColumnL2810PartBCDFG1810, n4QuarticColumnL2810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnL2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : 4 * C.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : 2 * C.natDegree + G.natDegree < d)
    (hd10 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd11 : 2 * G.natDegree < d) :
    (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnL2810_split_of_live_BCDFG l A B C D E F G hEz]
  exact (natDegree_add_lt810 (n4QuarticColumnL2810PartBCDFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnL2810PartBCDFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n4QuarticColumnBeta1810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnBeta1810PartBCDFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7
  + (35 / 131072 * beta : k) • (A ^ 5 * C)
  - (49 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  - (7 / 4096 * beta : k) • (A ^ 3 * B * D)
  + (21 / 8192 * beta : k) • (A ^ 3 * C ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCDFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnBeta1810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n4QuarticColumnBeta1810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnBeta1810PartBCDFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (427 / 32768 * beta : k) • (A * B ^ 4)
  - (7 / 256 * beta : k) • (A ^ 2 * D ^ 2)
  - (35 / 256 * beta : k) • (A * B * C * D)
  - (7 / 512 * beta : k) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + D.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCDFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnBeta1810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n4QuarticColumnBeta1810` on the live set `BCDFG` (2 monomials). -/
def n4QuarticColumnBeta1810PartBCDFG3810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (A * D * F)
  + (7 / 32 * beta : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810PartBCDFG3810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n4QuarticColumnBeta1810PartBCDFG3810 beta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnBeta1810PartBCDFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_split_of_live_BCDFG
    (beta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n4QuarticColumnBeta1810 beta A B C D E F G =
      n4QuarticColumnBeta1810PartBCDFG1810 beta A B C D E F G +
        n4QuarticColumnBeta1810PartBCDFG2810 beta A B C D E F G +
        n4QuarticColumnBeta1810PartBCDFG3810 beta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnBeta1810, n4QuarticColumnBeta1810PartBCDFG1810, n4QuarticColumnBeta1810PartBCDFG2810, n4QuarticColumnBeta1810PartBCDFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta1810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (beta : k)
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
    (hd7 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 3 * C.natDegree < d)
    (hd10 : 3 * B.natDegree + D.natDegree < d)
    (hd11 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd12 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + F.natDegree < d) :
    (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnBeta1810_split_of_live_BCDFG beta A B C D E F G hEz]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticColumnBeta1810PartBCDFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnBeta1810PartBCDFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticColumnBeta1810PartBCDFG3810_natDegree_lt beta A B C D E F G hdpos hd12 hd13))

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnBeta2810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
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
/-- Piece 1/2 of `n4QuarticColumnGamma810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnGamma810PartBCDFG1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 64 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 32 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * B.natDegree + F.natDegree < d) :
    (n4QuarticColumnGamma810PartBCDFG1810 gamma A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnGamma810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnGamma810` on the live set `BCDFG` (2 monomials). -/
def n4QuarticColumnGamma810PartBCDFG2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * C.natDegree + D.natDegree < d) :
    (n4QuarticColumnGamma810PartBCDFG2810 gamma A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnGamma810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_split_of_live_BCDFG
    (gamma : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n4QuarticColumnGamma810 gamma A B C D E F G =
      n4QuarticColumnGamma810PartBCDFG1810 gamma A B C D E F G +
        n4QuarticColumnGamma810PartBCDFG2810 gamma A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnGamma810, n4QuarticColumnGamma810PartBCDFG1810, n4QuarticColumnGamma810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnGamma810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * B.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * C.natDegree + D.natDegree < d) :
    (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnGamma810_split_of_live_BCDFG gamma A B C D E F G hEz]
  exact (natDegree_add_lt810 (n4QuarticColumnGamma810PartBCDFG1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnGamma810PartBCDFG2810_natDegree_lt gamma A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n4QuarticColumnDelta810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnDelta810PartBCDFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6
  + (15 / 16384 * delta : k) • (A ^ 4 * C)
  - (5 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  - (25 / 512 * delta : k) • (A ^ 2 * B * D)
  + (5 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (155 / 1024 * delta : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCDFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (n4QuarticColumnDelta810PartBCDFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnDelta810PartBCDFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n4QuarticColumnDelta810` on the live set `BCDFG` (6 monomials). -/
def n4QuarticColumnDelta810PartBCDFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(135 / 4096 * delta : k)) • B ^ 4
  + (5 / 64 * delta : k) • (A * B * F)
  + (25 / 128 * delta : k) • (A * D ^ 2)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810PartBCDFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 2 * D.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 3 * C.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (n4QuarticColumnDelta810PartBCDFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n4QuarticColumnDelta810PartBCDFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_split_of_live_BCDFG
    (delta : k)
    (A B C D E F G : k[X])
    (hEz : E = 0) :
    n4QuarticColumnDelta810 delta A B C D E F G =
      n4QuarticColumnDelta810PartBCDFG1810 delta A B C D E F G +
        n4QuarticColumnDelta810PartBCDFG2810 delta A B C D E F G := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnDelta810, n4QuarticColumnDelta810PartBCDFG1810, n4QuarticColumnDelta810PartBCDFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnDelta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : 3 * C.natDegree < d)
    (hd11 : D.natDegree + F.natDegree < d) :
    (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n4QuarticColumnDelta810_split_of_live_BCDFG delta A B C D E F G hEz]
  exact (natDegree_add_lt810 (n4QuarticColumnDelta810PartBCDFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticColumnDelta810PartBCDFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))


end QuarticChamberUnownedSystemColumns7810

end Max11DegreeRoutes
