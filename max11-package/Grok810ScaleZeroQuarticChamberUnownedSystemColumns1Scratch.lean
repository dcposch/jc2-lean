import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch

/-! # UnownedSystem load-column bounds, part 1/10

57 of the 403 (carrier, load, live-set) column bounds the
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

section QuarticChamberUnownedSystemColumns1810

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + G.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d) :
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * B.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree < d)
    (hd2 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + B.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [nuQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : A.natDegree + 4 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + G.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d) :
    (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL2810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : 4 * B.natDegree < d) :
    (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_natDegree_lt_of_live_BG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d) :
    (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * B.natDegree < d) :
    (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnZeta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree < d)
    (hd2 : G.natDegree < d) :
    (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + B.natDegree < d) :
    (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnTheta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d) :
    (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [omicronQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + G.natDegree < d) :
    (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd1 : 2 * G.natDegree < d) :
    (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : A.natDegree + 4 * B.natDegree < d) :
    (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_natDegree_lt_of_live_BG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d) :
    (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : 4 * B.natDegree < d) :
    (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnZeta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d) :
    (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree + B.natDegree < d)
    (hd1 : 3 * B.natDegree < d) :
    (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnTheta810_natDegree_lt_of_live_BG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree < d)
    (hd2 : G.natDegree < d) :
    (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hCz
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
  simp only [primitiveQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticColumnL810` on the live set `BCF` (6 monomials). -/
def nuQuarticColumnL810PartBCF1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  - (9 / 256 * l : k) • (A * B * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810PartBCF1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd4 : 4 * B.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + F.natDegree < d) :
    (nuQuarticColumnL810PartBCF1810 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticColumnL810` on the live set `BCF` (1 monomials). -/
def nuQuarticColumnL810PartBCF2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(21 / 1024 * l : k)) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810PartBCF2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d) :
    (nuQuarticColumnL810PartBCF2810 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_split_of_live_BCF
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    nuQuarticColumnL810 l A B C D E F G =
      nuQuarticColumnL810PartBCF1810 l A B C D E F G +
        nuQuarticColumnL810PartBCF2810 l A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnL810, nuQuarticColumnL810PartBCF1810, nuQuarticColumnL810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd4 : 4 * B.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd6 : 3 * C.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  rw [nuQuarticColumnL810_split_of_live_BCF l A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (nuQuarticColumnL810PartBCF1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticColumnL810PartBCF2810_natDegree_lt l A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree < d)
    (hd4 : B.natDegree + F.natDegree < d) :
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * C.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + B.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnL1810` on the live set `BCF` (6 monomials). -/
def omicronQuarticColumnL1810PartBCF1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 33554432 * l : k) • A ^ 7
  + (225 / 2097152 * l : k) • (A ^ 5 * C)
  - (171 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (99 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  - (45 / 131072 * l : k) • (A ^ 2 * B ^ 2 * C)
  - (189 / 65536 * l : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCF1810_natDegree_lt
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
    (omicronQuarticColumnL1810PartBCF1810 l A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnL1810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnL1810` on the live set `BCF` (4 monomials). -/
def omicronQuarticColumnL1810PartBCF2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 4096 * l : k)) • (A ^ 2 * B * F)
  + (9 / 8192 * l : k) • (A * C ^ 3)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  - (9 / 128 * l : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810PartBCF2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + 3 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnL1810PartBCF2810 l A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnL1810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_split_of_live_BCF
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    omicronQuarticColumnL1810 l A B C D E F G =
      omicronQuarticColumnL1810PartBCF1810 l A B C D E F G +
        omicronQuarticColumnL1810PartBCF2810 l A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnL1810, omicronQuarticColumnL1810PartBCF1810, omicronQuarticColumnL1810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL1810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
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
    (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnL1810_split_of_live_BCF l A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (omicronQuarticColumnL1810PartBCF1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnL1810PartBCF2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnL2810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * F.natDegree < d) :
    (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `omicronQuarticColumnBeta810` on the live set `BCF` (6 monomials). -/
def omicronQuarticColumnBeta810PartBCF1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 2097152 * beta : k) • A ^ 6
  + (49 / 131072 * beta : k) • (A ^ 4 * C)
  - (35 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (21 / 8192 * beta : k) • (A ^ 2 * C ^ 2)
  - (91 / 8192 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCF1810_natDegree_lt
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
    (omicronQuarticColumnBeta810PartBCF1810 beta A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnBeta810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `omicronQuarticColumnBeta810` on the live set `BCF` (1 monomials). -/
def omicronQuarticColumnBeta810PartBCF2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 512 * beta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810PartBCF2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d) :
    (omicronQuarticColumnBeta810PartBCF2810 beta A B C D E F G).natDegree < d := by
  simp only [omicronQuarticColumnBeta810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_split_of_live_BCF
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    omicronQuarticColumnBeta810 beta A B C D E F G =
      omicronQuarticColumnBeta810PartBCF1810 beta A B C D E F G +
        omicronQuarticColumnBeta810PartBCF2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnBeta810, omicronQuarticColumnBeta810PartBCF1810, omicronQuarticColumnBeta810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnBeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 3 * C.natDegree < d) :
    (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [omicronQuarticColumnBeta810_split_of_live_BCF beta A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (omicronQuarticColumnBeta810PartBCF1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticColumnBeta810PartBCF2810_natDegree_lt beta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnGamma810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * C.natDegree < d)
    (hd4 : C.natDegree + F.natDegree < d) :
    (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnDelta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree < d)
    (hd5 : B.natDegree + F.natDegree < d) :
    (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d) :
    (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
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
theorem omicronQuarticColumnZeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * C.natDegree < d) :
    (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
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
theorem omicronQuarticColumnEta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + B.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
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
theorem omicronQuarticColumnTheta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : A.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree < d) :
    (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
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
/-- Piece 1/2 of `piQuarticColumnL1810` on the live set `BCF` (6 monomials). -/
def piQuarticColumnL1810PartBCF1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810PartBCF1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 4 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd5 : 5 * B.natDegree < d) :
    (piQuarticColumnL1810PartBCF1810 l A B C D E F G).natDegree < d := by
  simp only [piQuarticColumnL1810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `piQuarticColumnL1810` on the live set `BCF` (3 monomials). -/
def piQuarticColumnL1810PartBCF2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(27 / 1024 * l : k)) • (A ^ 2 * C * F)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (63 / 512 * l : k) • (B * C ^ 3)

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810PartBCF2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + 3 * C.natDegree < d) :
    (piQuarticColumnL1810PartBCF2810 l A B C D E F G).natDegree < d := by
  simp only [piQuarticColumnL1810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810_split_of_live_BCF
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    piQuarticColumnL1810 l A B C D E F G =
      piQuarticColumnL1810PartBCF1810 l A B C D E F G +
        piQuarticColumnL1810PartBCF2810 l A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnL1810, piQuarticColumnL1810PartBCF1810, piQuarticColumnL1810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 4 * A.natDegree + F.natDegree < d)
    (hd3 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd5 : 5 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + 3 * C.natDegree < d) :
    (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [piQuarticColumnL1810_split_of_live_BCF l A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (piQuarticColumnL1810PartBCF1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticColumnL1810PartBCF2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL2810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree + F.natDegree < d) :
    (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `piQuarticColumnBeta810` on the live set `BCF` (6 monomials). -/
def piQuarticColumnBeta810PartBCF1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810PartBCF1810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticColumnBeta810PartBCF1810 beta A B C D E F G).natDegree < d := by
  simp only [piQuarticColumnBeta810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `piQuarticColumnBeta810` on the live set `BCF` (1 monomials). -/
def piQuarticColumnBeta810PartBCF2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 128 * beta : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810PartBCF2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + F.natDegree < d) :
    (piQuarticColumnBeta810PartBCF2810 beta A B C D E F G).natDegree < d := by
  simp only [piQuarticColumnBeta810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810_split_of_live_BCF
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    piQuarticColumnBeta810 beta A B C D E F G =
      piQuarticColumnBeta810PartBCF1810 beta A B C D E F G +
        piQuarticColumnBeta810PartBCF2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnBeta810, piQuarticColumnBeta810PartBCF1810, piQuarticColumnBeta810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + F.natDegree < d) :
    (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [piQuarticColumnBeta810_split_of_live_BCF beta A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (piQuarticColumnBeta810PartBCF1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticColumnBeta810PartBCF2810_natDegree_lt beta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnGamma810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 3 * C.natDegree < d) :
    (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnDelta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * C.natDegree < d)
    (hd4 : C.natDegree + F.natDegree < d) :
    (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEpsilon810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + C.natDegree < d)
    (hd1 : B.natDegree + F.natDegree < d) :
    (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnZeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d) :
    (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree < d)
    (hd1 : 2 * C.natDegree < d) :
    (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnTheta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : B.natDegree + C.natDegree < d)
    (hd1 : F.natDegree < d) :
    (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnL1810` on the live set `BCF` (6 monomials). -/
def primitiveQuarticColumnL1810PartBCF1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCF1810_natDegree_lt
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
    (primitiveQuarticColumnL1810PartBCF1810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL1810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnL1810` on the live set `BCF` (4 monomials). -/
def primitiveQuarticColumnL1810PartBCF2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 4096 * l : k)) • (A ^ 3 * B * F)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810PartBCF2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d) :
    (primitiveQuarticColumnL1810PartBCF2810 l A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnL1810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_split_of_live_BCF
    (l : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    primitiveQuarticColumnL1810 l A B C D E F G =
      primitiveQuarticColumnL1810PartBCF1810 l A B C D E F G +
        primitiveQuarticColumnL1810PartBCF2810 l A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnL1810, primitiveQuarticColumnL1810PartBCF1810, primitiveQuarticColumnL1810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL1810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 8 * A.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd6 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd7 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd8 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd9 : 4 * B.natDegree + C.natDegree < d) :
    (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnL1810_split_of_live_BCF l A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (primitiveQuarticColumnL1810PartBCF1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnL1810PartBCF2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnL2810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : 3 * B.natDegree + F.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : A.natDegree + 2 * F.natDegree < d) :
    (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnBeta810` on the live set `BCF` (6 monomials). -/
def primitiveQuarticColumnBeta810PartBCF1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCF1810_natDegree_lt
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
    (primitiveQuarticColumnBeta810PartBCF1810 beta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnBeta810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnBeta810` on the live set `BCF` (3 monomials). -/
def primitiveQuarticColumnBeta810PartBCF2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(91 / 1024 * beta : k)) • (B ^ 2 * C ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  - (7 / 16 * beta : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810PartBCF2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (primitiveQuarticColumnBeta810PartBCF2810 beta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnBeta810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_split_of_live_BCF
    (beta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    primitiveQuarticColumnBeta810 beta A B C D E F G =
      primitiveQuarticColumnBeta810PartBCF1810 beta A B C D E F G +
        primitiveQuarticColumnBeta810PartBCF2810 beta A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnBeta810, primitiveQuarticColumnBeta810PartBCF1810, primitiveQuarticColumnBeta810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 7 * A.natDegree < d)
    (hd1 : 5 * A.natDegree + C.natDegree < d)
    (hd2 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnBeta810_split_of_live_BCF beta A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (primitiveQuarticColumnBeta810PartBCF1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnBeta810PartBCF2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnGamma810` on the live set `BCF` (6 monomials). -/
def primitiveQuarticColumnGamma810PartBCF1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810PartBCF1810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnGamma810PartBCF1810 gamma A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnGamma810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnGamma810` on the live set `BCF` (1 monomials). -/
def primitiveQuarticColumnGamma810PartBCF2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * gamma : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810PartBCF2810_natDegree_lt
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnGamma810PartBCF2810 gamma A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnGamma810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_split_of_live_BCF
    (gamma : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    primitiveQuarticColumnGamma810 gamma A B C D E F G =
      primitiveQuarticColumnGamma810PartBCF1810 gamma A B C D E F G +
        primitiveQuarticColumnGamma810PartBCF2810 gamma A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnGamma810, primitiveQuarticColumnGamma810PartBCF1810, primitiveQuarticColumnGamma810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd2 : 3 * A.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnGamma810_split_of_live_BCF gamma A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (primitiveQuarticColumnGamma810PartBCF1810_natDegree_lt gamma A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnGamma810PartBCF2810_natDegree_lt gamma A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticColumnDelta810` on the live set `BCF` (6 monomials). -/
def primitiveQuarticColumnDelta810PartBCF1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCF1810_natDegree_lt
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
    (primitiveQuarticColumnDelta810PartBCF1810 delta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnDelta810PartBCF1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticColumnDelta810` on the live set `BCF` (1 monomials). -/
def primitiveQuarticColumnDelta810PartBCF2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 64 * delta : k) • C ^ 3

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810PartBCF2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree < d) :
    (primitiveQuarticColumnDelta810PartBCF2810 delta A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticColumnDelta810PartBCF2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_split_of_live_BCF
    (delta : k)
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    primitiveQuarticColumnDelta810 delta A B C D E F G =
      primitiveQuarticColumnDelta810PartBCF1810 delta A B C D E F G +
        primitiveQuarticColumnDelta810PartBCF2810 delta A B C D E F G := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnDelta810, primitiveQuarticColumnDelta810PartBCF1810, primitiveQuarticColumnDelta810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 3 * C.natDegree < d) :
    (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [primitiveQuarticColumnDelta810_split_of_live_BCF delta A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (primitiveQuarticColumnDelta810PartBCF1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticColumnDelta810PartBCF2810_natDegree_lt delta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * C.natDegree < d)
    (hd4 : C.natDegree + F.natDegree < d) :
    (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega


end QuarticChamberUnownedSystemColumns1810

end Max11DegreeRoutes
