import Grok810ScaleZeroQuarticChamberNuFacesScratch

/-! # Load-column bounds for the carrier-change kills, `(8,10)` scale zero

The further (carrier, load, live-set) column bounds the corner-`H` carrier change needs.  Untracked working note.
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

section QuarticChamberColumns3810

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810_natDegree_lt_of_live_DF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * A.natDegree + F.natDegree < d) :
    (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL2810_natDegree_lt_of_live_DF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * D.natDegree < d) :
    (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810_natDegree_lt_of_live_DF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree + F.natDegree < d) :
    (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnGamma810_natDegree_lt_of_live_DF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnDelta810_natDegree_lt_of_live_DF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + F.natDegree < d) :
    (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEpsilon810_natDegree_lt_of_live_DF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * D.natDegree < d) :
    (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnZeta810_natDegree_lt_of_live_DF
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + F.natDegree < d) :
    (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnTheta810_natDegree_lt_of_live_DF
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : F.natDegree < d) :
    (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL1810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * A.natDegree + F.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnL2810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree + F.natDegree < d)
    (hd1 : 3 * D.natDegree < d) :
    (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnBeta810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * A.natDegree + F.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 2 * C.natDegree + D.natDegree < d) :
    (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnGamma810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnDelta810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEpsilon810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * D.natDegree < d) :
    (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnZeta810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree < d) :
    (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnEta810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree < d) :
    (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticColumnTheta810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : F.natDegree < d) :
    (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd2 : 4 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + 2 * D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : B.natDegree + F.natDegree < d)
    (hd4 : 2 * D.natDegree < d) :
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 3 * B.natDegree < d)
    (hd1 : A.natDegree + F.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree < d)
    (hd2 : B.natDegree + D.natDegree < d)
    (hd3 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnEpsilon810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : F.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
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

def nuQuarticColumnL810_liveBCDFG_Columns3c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBCDFG_Columns3c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (nuQuarticColumnL810_liveBCDFG_Columns3c1 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBCDFG_Columns3c1]
  compute_degree
  omega

def nuQuarticColumnL810_liveBCDFG_Columns3c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 512 * l : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBCDFG_Columns3c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + C.natDegree + D.natDegree < d) :
    (nuQuarticColumnL810_liveBCDFG_Columns3c2 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBCDFG_Columns3c2]
  compute_degree
  omega

def nuQuarticColumnL810_liveBCDFG_Columns3c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((21 / 1024 * l : k) • C ^ 3)
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBCDFG_Columns3c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 3 * C.natDegree < d)
    (hd11 : C.natDegree + G.natDegree < d)
    (hd12 : D.natDegree + F.natDegree < d) :
    (nuQuarticColumnL810_liveBCDFG_Columns3c3 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBCDFG_Columns3c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 4 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : 4 * B.natDegree < d)
    (hd6 : 2 * A.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : 3 * C.natDegree < d)
    (hd11 : C.natDegree + G.natDegree < d)
    (hd12 : D.natDegree + F.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : nuQuarticColumnL810 l A B C D 0 F G = nuQuarticColumnL810_liveBCDFG_Columns3c1 l A B C D 0 F G + nuQuarticColumnL810_liveBCDFG_Columns3c2 l A B C D 0 F G + nuQuarticColumnL810_liveBCDFG_Columns3c3 l A B C D 0 F G := by
    simp only [nuQuarticColumnL810, nuQuarticColumnL810_liveBCDFG_Columns3c1, nuQuarticColumnL810_liveBCDFG_Columns3c2, nuQuarticColumnL810_liveBCDFG_Columns3c3, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticColumnL810_liveBCDFG_Columns3c1_natDegree_lt l A B C D 0 F G hdpos hd0 hd1 hd2 hd3 hd4) (nuQuarticColumnL810_liveBCDFG_Columns3c2_natDegree_lt l A B C D 0 F G hdpos hd5 hd6 hd7 hd8 hd9))) (nuQuarticColumnL810_liveBCDFG_Columns3c3_natDegree_lt l A B C D 0 F G hdpos hd10 hd11 hd12)))


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (beta : k)
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
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hEz
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
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + D.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hEz
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
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hEz
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
theorem nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hEz
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
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hEz
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
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hEz
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
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hEz
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

def nuQuarticColumnL810_liveBDEFG_Columns3c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBDEFG_Columns3c1_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : 4 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d) :
    (nuQuarticColumnL810_liveBDEFG_Columns3c1 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBDEFG_Columns3c1]
  compute_degree
  omega

def nuQuarticColumnL810_liveBDEFG_Columns3c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 256 * l : k) • (A * B * F))
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBDEFG_Columns3c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * B.natDegree + E.natDegree < d)
    (hd8 : D.natDegree + F.natDegree < d)
    (hd9 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810_liveBDEFG_Columns3c2 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBDEFG_Columns3c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 6 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : 4 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * B.natDegree + E.natDegree < d)
    (hd8 : D.natDegree + F.natDegree < d)
    (hd9 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : nuQuarticColumnL810 l A B 0 D E F G = nuQuarticColumnL810_liveBDEFG_Columns3c1 l A B 0 D E F G + nuQuarticColumnL810_liveBDEFG_Columns3c2 l A B 0 D E F G := by
    simp only [nuQuarticColumnL810, nuQuarticColumnL810_liveBDEFG_Columns3c1, nuQuarticColumnL810_liveBDEFG_Columns3c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticColumnL810_liveBDEFG_Columns3c1_natDegree_lt l A B 0 D E F G hdpos hd0 hd1 hd2 hd3 hd4) (nuQuarticColumnL810_liveBDEFG_Columns3c2_natDegree_lt l A B 0 D E F G hdpos hd5 hd6 hd7 hd8 hd9)))


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd4 : B.natDegree + F.natDegree < d)
    (hd5 : 2 * D.natDegree < d) :
    (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
  subst hCz
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
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 3 * B.natDegree < d)
    (hd1 : A.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + E.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
  subst hCz
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
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree < d)
    (hd2 : B.natDegree + D.natDegree < d)
    (hd3 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
  subst hCz
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
theorem nuQuarticColumnEpsilon810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : F.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
  subst hCz
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
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d)
    (hd2 : E.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
  subst hCz
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
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
  subst hCz
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
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : 2 * A.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
  subst hCz
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

def nuQuarticColumnL810_liveBCDEFG_Columns3c1
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (105 / 4194304 * l : k) • A ^ 6
  + (135 / 262144 * l : k) • (A ^ 4 * C)
  + (9 / 4096 * l : k) • (A ^ 3 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (9 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 4096 * l : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBCDEFG_Columns3c1_natDegree_lt
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
    (nuQuarticColumnL810_liveBCDEFG_Columns3c1 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBCDEFG_Columns3c1]
  compute_degree
  omega

def nuQuarticColumnL810_liveBCDEFG_Columns3c2
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  (315 / 32768 * l : k) • B ^ 4
  + (9 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * F)
  - (9 / 512 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)
  - (63 / 512 * l : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBCDEFG_Columns3c2_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : 4 * B.natDegree < d)
    (hd7 : 2 * A.natDegree + G.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd9 : A.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * B.natDegree + E.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + D.natDegree < d) :
    (nuQuarticColumnL810_liveBCDEFG_Columns3c2 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBCDEFG_Columns3c2]
  compute_degree
  omega

def nuQuarticColumnL810_liveBCDEFG_Columns3c3
    (l : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((21 / 1024 * l : k) • C ^ 3)
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_liveBCDEFG_Columns3c3_natDegree_lt
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : 3 * C.natDegree < d)
    (hd13 : C.natDegree + G.natDegree < d)
    (hd14 : D.natDegree + F.natDegree < d)
    (hd15 : 2 * E.natDegree < d) :
    (nuQuarticColumnL810_liveBCDEFG_Columns3c3 l A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnL810_liveBCDEFG_Columns3c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnL810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  have hsplit : nuQuarticColumnL810 l A B C D E F G = nuQuarticColumnL810_liveBCDEFG_Columns3c1 l A B C D E F G + nuQuarticColumnL810_liveBCDEFG_Columns3c2 l A B C D E F G + nuQuarticColumnL810_liveBCDEFG_Columns3c3 l A B C D E F G := by
    simp only [nuQuarticColumnL810, nuQuarticColumnL810_liveBCDEFG_Columns3c1, nuQuarticColumnL810_liveBCDEFG_Columns3c2, nuQuarticColumnL810_liveBCDEFG_Columns3c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticColumnL810_liveBCDEFG_Columns3c1_natDegree_lt l A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticColumnL810_liveBCDEFG_Columns3c2_natDegree_lt l A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))) (nuQuarticColumnL810_liveBCDEFG_Columns3c3_natDegree_lt l A B C D E F G hdpos hd12 hd13 hd14 hd15)))


def nuQuarticColumnBeta810_liveBCDEFG_Columns3c1
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 65536 * beta : k) • A ^ 5
  + (7 / 4096 * beta : k) • (A ^ 3 * C)
  - (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (7 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_liveBCDEFG_Columns3c1_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 5 * A.natDegree < d)
    (hd1 : 3 * A.natDegree + C.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree < d) :
    (nuQuarticColumnBeta810_liveBCDEFG_Columns3c1 beta A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnBeta810_liveBCDEFG_Columns3c1]
  compute_degree
  omega

def nuQuarticColumnBeta810_liveBCDEFG_Columns3c2
    (beta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (63 / 1024 * beta : k) • (B ^ 2 * C)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_liveBCDEFG_Columns3c2_natDegree_lt
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree < d)
    (hd6 : B.natDegree + F.natDegree < d)
    (hd7 : C.natDegree + E.natDegree < d)
    (hd8 : 2 * D.natDegree < d) :
    (nuQuarticColumnBeta810_liveBCDEFG_Columns3c2 beta A B C D E F G).natDegree < d := by
  simp only [nuQuarticColumnBeta810_liveBCDEFG_Columns3c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (beta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
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
  have hsplit : nuQuarticColumnBeta810 beta A B C D E F G = nuQuarticColumnBeta810_liveBCDEFG_Columns3c1 beta A B C D E F G + nuQuarticColumnBeta810_liveBCDEFG_Columns3c2 beta A B C D E F G := by
    simp only [nuQuarticColumnBeta810, nuQuarticColumnBeta810_liveBCDEFG_Columns3c1, nuQuarticColumnBeta810_liveBCDEFG_Columns3c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (nuQuarticColumnBeta810_liveBCDEFG_Columns3c1_natDegree_lt beta A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (nuQuarticColumnBeta810_liveBCDEFG_Columns3c2_natDegree_lt beta A B C D E F G hdpos hd5 hd6 hd7 hd8)))


set_option maxHeartbeats 64000000 in
theorem nuQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree < d)
    (hd2 : A.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
theorem nuQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (delta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree < d)
    (hd1 : 2 * A.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree < d)
    (hd3 : B.natDegree + D.natDegree < d)
    (hd4 : 2 * C.natDegree < d)
    (hd5 : G.natDegree < d) :
    (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
theorem nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + C.natDegree < d)
    (hd2 : F.natDegree < d) :
    (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
theorem nuQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (zeta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree < d)
    (hd1 : 2 * B.natDegree < d)
    (hd2 : E.natDegree < d) :
    (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
theorem nuQuarticColumnEta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (eta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree < d)
    (hd1 : D.natDegree < d) :
    (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
theorem nuQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree < d)
    (hd1 : C.natDegree < d) :
    (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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


end QuarticChamberColumns3810

end Max11DegreeRoutes
