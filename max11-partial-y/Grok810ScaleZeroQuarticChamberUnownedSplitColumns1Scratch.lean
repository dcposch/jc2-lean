import Grok810ScaleZeroQuarticChamberFacesPart0Scratch
import Grok810ScaleZeroQuarticChamberInfraN6Scratch

/-! # UnownedSplit load-column bounds, part 1/1

30 of the 30 (carrier, load, live-set) column bounds the
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

section QuarticChamberUnownedSplitColumns1810

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnL810_natDegree_lt_of_live_DG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree + D.natDegree < d) :
    (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnBeta810_natDegree_lt_of_live_DG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + D.natDegree < d) :
    (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGamma810_natDegree_lt_of_live_DG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : G.natDegree < d) :
    (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnDelta810_natDegree_lt_of_live_DG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + D.natDegree < d) :
    (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnZeta810_natDegree_lt_of_live_DG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : D.natDegree < d) :
    (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnL810_natDegree_lt_of_live_EF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + F.natDegree < d) :
    (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnBeta810_natDegree_lt_of_live_EF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + F.natDegree < d) :
    (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnDelta810_natDegree_lt_of_live_EF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : F.natDegree < d) :
    (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnEpsilon810_natDegree_lt_of_live_EF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : E.natDegree < d) :
    (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEpsilon810_natDegree_lt_of_live_EG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : G.natDegree < d) :
    (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
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
  simp only [xiQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEta810_natDegree_lt_of_live_EG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : E.natDegree < d) :
    (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
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
  simp only [xiQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGamma810_natDegree_lt_of_live_EG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : G.natDegree < d) :
    (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
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
  simp only [muQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnEpsilon810_natDegree_lt_of_live_EG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : E.natDegree < d) :
    (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
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
  simp only [muQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnL810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + E.natDegree < d)
    (hd2 : 2 * D.natDegree < d) :
    (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnBeta810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + E.natDegree < d) :
    (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnGamma810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : F.natDegree < d) :
    (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnDelta810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : E.natDegree < d) :
    (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnEpsilon810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree < d) :
    (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnZeta810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree < d) :
    (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticColumnTheta810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree < d) :
    (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnL1810` on the live set `CDEFG` (6 monomials). -/
def n6QuarticColumnL1810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • A ^ 8
  + (105 / 1048576 * l : k) • (A ^ 6 * C)
  + (105 / 262144 * l : k) • (A ^ 5 * E)
  + (585 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  + (15 / 32768 * l : k) • (A ^ 4 * G)
  + (81 / 8192 * l : k) • (A ^ 3 * C * E)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810PartCDEFG1810_natDegree_lt
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
    (n6QuarticColumnL1810PartCDEFG1810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL1810PartCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnL1810` on the live set `CDEFG` (5 monomials). -/
def n6QuarticColumnL1810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 8192 * l : k)) • (A ^ 3 * D ^ 2)
  + (11 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  + (3 / 256 * l : k) • (A ^ 2 * C * G)
  + (3 / 1024 * l : k) • (A ^ 2 * D * F)
  + (51 / 2048 * l : k) • (A ^ 2 * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd3 : 2 * A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * E.natDegree < d) :
    (n6QuarticColumnL1810PartCDEFG2810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL1810PartCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810_split_of_live_CDEFG
    (l : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n6QuarticColumnL1810 l A B C D E F G =
      n6QuarticColumnL1810PartCDEFG1810 l A B C D E F G +
        n6QuarticColumnL1810PartCDEFG2810 l A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnL1810, n6QuarticColumnL1810PartCDEFG1810, n6QuarticColumnL1810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL1810_natDegree_lt_of_live_CDEFG
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
    (n6QuarticColumnL1810 l A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnL1810_split_of_live_CDEFG l A B C D E F G hBz]
  exact natDegree_add_lt810 (n6QuarticColumnL1810PartCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnL1810PartCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnL2810` on the live set `CDEFG` (6 monomials). -/
def n6QuarticColumnL2810PartCDEFG1810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (39 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 128 * l : k) • (A * C * D ^ 2)
  + (63 / 4096 * l : k) • C ^ 4
  + (3 / 64 * l : k) • (A * E * G)
  - (3 / 16 * l : k) • (A * F ^ 2)
  - (9 / 128 * l : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d) :
    (n6QuarticColumnL2810PartCDEFG1810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL2810PartCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnL2810` on the live set `CDEFG` (4 monomials). -/
def n6QuarticColumnL2810PartCDEFG2810
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 32 * l : k)) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + 2 * E.natDegree < d)
    (hd2 : 2 * D.natDegree + E.natDegree < d)
    (hd3 : 2 * G.natDegree < d) :
    (n6QuarticColumnL2810PartCDEFG2810 l A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnL2810PartCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810_split_of_live_CDEFG
    (l : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n6QuarticColumnL2810 l A B C D E F G =
      n6QuarticColumnL2810PartCDEFG1810 l A B C D E F G +
        n6QuarticColumnL2810PartCDEFG2810 l A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnL2810, n6QuarticColumnL2810PartCDEFG1810, n6QuarticColumnL2810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnL2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : 2 * C.natDegree + G.natDegree < d)
    (hd6 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + 2 * E.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (n6QuarticColumnL2810 l A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnL2810_split_of_live_CDEFG l A B C D E F G hBz]
  exact natDegree_add_lt810 (n6QuarticColumnL2810PartCDEFG1810_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnL2810PartCDEFG2810_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9)

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticColumnBeta1810` on the live set `CDEFG` (6 monomials). -/
def n6QuarticColumnBeta1810PartCDEFG1810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • A ^ 7
  + (35 / 98304 * beta : k) • (A ^ 5 * C)
  + (35 / 24576 * beta : k) • (A ^ 4 * E)
  + (7 / 2048 * beta : k) • (A ^ 3 * C ^ 2)
  + (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  - (133 / 6144 * beta : k) • (A ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810PartCDEFG1810_natDegree_lt
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
    (n6QuarticColumnBeta1810PartCDEFG1810 beta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnBeta1810PartCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnBeta1810` on the live set `CDEFG` (3 monomials). -/
def n6QuarticColumnBeta1810PartCDEFG2810
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 768 * beta : k)) • (A * C ^ 3)
  + (7 / 96 * beta : k) • (A * D * F)
  + (7 / 48 * beta : k) • (A * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * C.natDegree < d)
    (hd1 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + 2 * E.natDegree < d) :
    (n6QuarticColumnBeta1810PartCDEFG2810 beta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnBeta1810PartCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810_split_of_live_CDEFG
    (beta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n6QuarticColumnBeta1810 beta A B C D E F G =
      n6QuarticColumnBeta1810PartCDEFG1810 beta A B C D E F G +
        n6QuarticColumnBeta1810PartCDEFG2810 beta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnBeta1810, n6QuarticColumnBeta1810PartCDEFG1810, n6QuarticColumnBeta1810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta1810_natDegree_lt_of_live_CDEFG
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
    (hd8 : A.natDegree + 2 * E.natDegree < d) :
    (n6QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnBeta1810_split_of_live_CDEFG beta A B C D E F G hBz]
  exact natDegree_add_lt810 (n6QuarticColumnBeta1810PartCDEFG1810_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnBeta1810PartCDEFG2810_natDegree_lt beta A B C D E F G hdpos hd6 hd7 hd8)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnBeta2810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (n6QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
  subst hBz
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
theorem n6QuarticColumnGamma810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 2 * C.natDegree + D.natDegree < d)
    (hd3 : E.natDegree + F.natDegree < d) :
    (n6QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hBz
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
/-- Piece 1/2 of `n6QuarticColumnDelta810` on the live set `CDEFG` (6 monomials). -/
def n6QuarticColumnDelta810PartCDEFG1810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 6
  + (5 / 4096 * delta : k) • (A ^ 4 * C)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  + (65 / 6144 * delta : k) • (A ^ 2 * C ^ 2)
  - (5 / 384 * delta : k) • (A ^ 2 * G)
  + (35 / 192 * delta : k) • (A * C * E)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 3 * A.natDegree + E.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + E.natDegree < d) :
    (n6QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnDelta810PartCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnDelta810` on the live set `CDEFG` (4 monomials). -/
def n6QuarticColumnDelta810PartCDEFG2810
    (delta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 * delta : k) • (A * D ^ 2)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (n6QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnDelta810PartCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810_split_of_live_CDEFG
    (delta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n6QuarticColumnDelta810 delta A B C D E F G =
      n6QuarticColumnDelta810PartCDEFG1810 delta A B C D E F G +
        n6QuarticColumnDelta810PartCDEFG2810 delta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnDelta810, n6QuarticColumnDelta810PartCDEFG1810, n6QuarticColumnDelta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnDelta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (delta : k)
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
    (hd8 : D.natDegree + F.natDegree < d)
    (hd9 : 2 * E.natDegree < d) :
    (n6QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnDelta810_split_of_live_CDEFG delta A B C D E F G hBz]
  exact natDegree_add_lt810 (n6QuarticColumnDelta810PartCDEFG1810_natDegree_lt delta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnDelta810PartCDEFG2810_natDegree_lt delta A B C D E F G hdpos hd6 hd7 hd8 hd9)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (n6QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
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
/-- Piece 1/2 of `n6QuarticColumnZeta810` on the live set `CDEFG` (6 monomials). -/
def n6QuarticColumnZeta810PartCDEFG1810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • A ^ 5
  + (1 / 256 * zeta : k) • (A ^ 3 * C)
  + (1 / 64 * zeta : k) • (A ^ 2 * E)
  + (3 / 64 * zeta : k) • (A * C ^ 2)
  - (1 / 4 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (C * E)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810PartCDEFG1810_natDegree_lt
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
    (n6QuarticColumnZeta810PartCDEFG1810 zeta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnZeta810PartCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticColumnZeta810` on the live set `CDEFG` (1 monomials). -/
def n6QuarticColumnZeta810PartCDEFG2810
    (zeta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * zeta : k)) • D ^ 2

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree < d) :
    (n6QuarticColumnZeta810PartCDEFG2810 zeta A B C D E F G).natDegree < d := by
  simp only [n6QuarticColumnZeta810PartCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810_split_of_live_CDEFG
    (zeta : k)
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n6QuarticColumnZeta810 zeta A B C D E F G =
      n6QuarticColumnZeta810PartCDEFG1810 zeta A B C D E F G +
        n6QuarticColumnZeta810PartCDEFG2810 zeta A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticColumnZeta810, n6QuarticColumnZeta810PartCDEFG1810, n6QuarticColumnZeta810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  module

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnZeta810_natDegree_lt_of_live_CDEFG
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
    (n6QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  rw [n6QuarticColumnZeta810_split_of_live_CDEFG zeta A B C D E F G hBz]
  exact natDegree_add_lt810 (n6QuarticColumnZeta810PartCDEFG1810_natDegree_lt zeta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticColumnZeta810PartCDEFG2810_natDegree_lt zeta A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem n6QuarticColumnEta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree < d) :
    (n6QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hBz
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
theorem n6QuarticColumnTheta810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + E.natDegree < d)
    (hd3 : 2 * C.natDegree < d)
    (hd4 : G.natDegree < d) :
    (n6QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hBz
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


end QuarticChamberUnownedSplitColumns1810

end Max11DegreeRoutes
