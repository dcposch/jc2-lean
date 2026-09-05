import Grok810ScaleZeroQuarticChamberFacesPart1Scratch

/-! # Cost-argmin rest bounds, part 8/10, `(8,10)` scale zero

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
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF11810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF11810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF11810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF11810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF11810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : A.natDegree + 2 * F.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF4810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF4810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF4810_liveBCDEFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF4810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + F.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd11 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF4810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF4810_liveBCDEFG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF4810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF4810_liveBCDEFG_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF4810_natDegree_lt_of_live_BCDEFG
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
    (hd12 : A.natDegree + 2 * F.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF4810 A B C D E F G).natDegree < d := by
  have hsplit : piQuarticChamberRestLF4810 A B C D E F G = piQuarticChamberRestLF4810_liveBCDEFG_p8c1 A B C D E F G + piQuarticChamberRestLF4810_liveBCDEFG_p8c2 A B C D E F G + piQuarticChamberRestLF4810_liveBCDEFG_p8c3 A B C D E F G := by
    simp only [piQuarticChamberRestLF4810, piQuarticChamberRestLF4810_liveBCDEFG_p8c1, piQuarticChamberRestLF4810_liveBCDEFG_p8c2, piQuarticChamberRestLF4810_liveBCDEFG_p8c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF4810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF4810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11))) (piQuarticChamberRestLF4810_liveBCDEFG_p8c3_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : D.natDegree + F.natDegree < d)
    (hd1 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d)
    (hd6 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : C.natDegree + G.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d)
    (hd2 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF12810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def muQuarticChamberRestLF12810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (15 / 128 : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF12810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [muQuarticChamberRestLF12810_liveBCDEFG_p8c1]
  compute_degree
  omega

def muQuarticChamberRestLF12810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 64 : k) • (B * C * D))
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [muQuarticChamberRestLF12810_liveBCDEFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF12810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + G.natDegree < d)
    (hd6 : D.natDegree + F.natDegree < d)
    (hd7 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF12810 A B C D E F G).natDegree < d := by
  have hsplit : muQuarticChamberRestLF12810 A B C D E F G = muQuarticChamberRestLF12810_liveBCDEFG_p8c1 A B C D E F G + muQuarticChamberRestLF12810_liveBCDEFG_p8c2 A B C D E F G := by
    simp only [muQuarticChamberRestLF12810, muQuarticChamberRestLF12810_liveBCDEFG_p8c1, muQuarticChamberRestLF12810_liveBCDEFG_p8c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (muQuarticChamberRestLF12810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3) (muQuarticChamberRestLF12810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd4 hd5 hd6 hd7)))

def piQuarticChamberRestLF5810_liveBCDE_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDE_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDE_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDE_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDE_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDE_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDE_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDE_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF5810 A B C D E 0 0 = piQuarticChamberRestLF5810_liveBCDE_p8c1 A B C D E 0 0 + piQuarticChamberRestLF5810_liveBCDE_p8c2 A B C D E 0 0 := by
    simp only [piQuarticChamberRestLF5810, piQuarticChamberRestLF5810_liveBCDE_p8c1, piQuarticChamberRestLF5810_liveBCDE_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF5810_liveBCDE_p8c1_natDegree_lt A B C D E 0 0 hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF5810_liveBCDE_p8c2_natDegree_lt A B C D E 0 0 hdpos hd5 hd6 hd7 hd8 hd9)))

def piQuarticChamberRestLF5810_liveBCDF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDF_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDF_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDF_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDF_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDF
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
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF5810 A B C D 0 F 0 = piQuarticChamberRestLF5810_liveBCDF_p8c1 A B C D 0 F 0 + piQuarticChamberRestLF5810_liveBCDF_p8c2 A B C D 0 F 0 := by
    simp only [piQuarticChamberRestLF5810, piQuarticChamberRestLF5810_liveBCDF_p8c1, piQuarticChamberRestLF5810_liveBCDF_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF5810_liveBCDF_p8c1_natDegree_lt A B C D 0 F 0 hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF5810_liveBCDF_p8c2_natDegree_lt A B C D 0 F 0 hdpos hd5 hd6 hd7 hd8 hd9)))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd2 : C.natDegree + 2 * E.natDegree < d)
    (hd3 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF5810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEF_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEF_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEF_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (A * F ^ 2))
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEF_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEF_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEF_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEF
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
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd9 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + 2 * F.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF5810 A B C D E F 0 = piQuarticChamberRestLF5810_liveBCDEF_p8c1 A B C D E F 0 + piQuarticChamberRestLF5810_liveBCDEF_p8c2 A B C D E F 0 + piQuarticChamberRestLF5810_liveBCDEF_p8c3 A B C D E F 0 := by
    simp only [piQuarticChamberRestLF5810, piQuarticChamberRestLF5810_liveBCDEF_p8c1, piQuarticChamberRestLF5810_liveBCDEF_p8c2, piQuarticChamberRestLF5810_liveBCDEF_p8c3, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF5810_liveBCDEF_p8c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF5810_liveBCDEF_p8c2_natDegree_lt A B C D E F 0 hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF5810_liveBCDEF_p8c3_natDegree_lt A B C D E F 0 hdpos hd10 hd11 hd12 hd13 hd14)))

def piQuarticChamberRestLF5810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (C ^ 2 * G))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEG_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * D.natDegree + E.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF5810 A B C D E 0 G = piQuarticChamberRestLF5810_liveBCDEG_p8c1 A B C D E 0 G + piQuarticChamberRestLF5810_liveBCDEG_p8c2 A B C D E 0 G + piQuarticChamberRestLF5810_liveBCDEG_p8c3 A B C D E 0 G := by
    simp only [piQuarticChamberRestLF5810, piQuarticChamberRestLF5810_liveBCDEG_p8c1, piQuarticChamberRestLF5810_liveBCDEG_p8c2, piQuarticChamberRestLF5810_liveBCDEG_p8c3, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF5810_liveBCDEG_p8c1_natDegree_lt A B C D E 0 G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF5810_liveBCDEG_p8c2_natDegree_lt A B C D E 0 G hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF5810_liveBCDEG_p8c3_natDegree_lt A B C D E 0 G hdpos hd10 hd11 hd12 hd13)))

def piQuarticChamberRestLF5810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDFG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDFG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDFG_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDFG
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
    (hd6 : 3 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF5810 A B C D 0 F G = piQuarticChamberRestLF5810_liveBCDFG_p8c1 A B C D 0 F G + piQuarticChamberRestLF5810_liveBCDFG_p8c2 A B C D 0 F G + piQuarticChamberRestLF5810_liveBCDFG_p8c3 A B C D 0 F G := by
    simp only [piQuarticChamberRestLF5810, piQuarticChamberRestLF5810_liveBCDFG_p8c1, piQuarticChamberRestLF5810_liveBCDFG_p8c2, piQuarticChamberRestLF5810_liveBCDFG_p8c3, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF5810_liveBCDFG_p8c1_natDegree_lt A B C D 0 F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF5810_liveBCDFG_p8c2_natDegree_lt A B C D 0 F G hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF5810_liveBCDFG_p8c3_natDegree_lt A B C D 0 F G hdpos hd10 hd11 hd12 hd13)))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * F.natDegree < d)
    (hd1 : 2 * C.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + 2 * E.natDegree < d)
    (hd4 : 2 * D.natDegree + E.natDegree < d)
    (hd5 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF5810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c3]
  compute_degree
  omega

def piQuarticChamberRestLF5810_liveBCDEFG_p8c4
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (C * D * F))
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_liveBCDEFG_p8c4_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810_liveBCDEFG_p8c4 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF5810_liveBCDEFG_p8c4]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5810_natDegree_lt_of_live_BCDEFG
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
    (hd7 : 3 * B.natDegree + F.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd10 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5810 A B C D E F G).natDegree < d := by
  have hsplit : piQuarticChamberRestLF5810 A B C D E F G = piQuarticChamberRestLF5810_liveBCDEFG_p8c1 A B C D E F G + piQuarticChamberRestLF5810_liveBCDEFG_p8c2 A B C D E F G + piQuarticChamberRestLF5810_liveBCDEFG_p8c3 A B C D E F G + piQuarticChamberRestLF5810_liveBCDEFG_p8c4 A B C D E F G := by
    simp only [piQuarticChamberRestLF5810, piQuarticChamberRestLF5810_liveBCDEFG_p8c1, piQuarticChamberRestLF5810_liveBCDEFG_p8c2, piQuarticChamberRestLF5810_liveBCDEFG_p8c3, piQuarticChamberRestLF5810_liveBCDEFG_p8c4, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF5810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF5810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF5810_liveBCDEFG_p8c3_natDegree_lt A B C D E F G hdpos hd10 hd11 hd12 hd13 hd14))) (piQuarticChamberRestLF5810_liveBCDEFG_p8c4_natDegree_lt A B C D E F G hdpos hd15 hd16 hd17 hd18)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF13810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF13810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF13810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF13810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd5 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF6810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEF_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF6810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEF_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF6810 A B C D E F 0 = piQuarticChamberRestLF6810_liveBCDEF_p8c1 A B C D E F 0 + piQuarticChamberRestLF6810_liveBCDEF_p8c2 A B C D E F 0 := by
    simp only [piQuarticChamberRestLF6810, piQuarticChamberRestLF6810_liveBCDEF_p8c1, piQuarticChamberRestLF6810_liveBCDEF_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF6810_liveBCDEF_p8c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF6810_liveBCDEF_p8c2_natDegree_lt A B C D E F 0 hdpos hd6 hd7 hd8 hd9 hd10)))

def piQuarticChamberRestLF6810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF6810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : 2 * D.natDegree + E.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF6810 A B C D E 0 G = piQuarticChamberRestLF6810_liveBCDEG_p8c1 A B C D E 0 G + piQuarticChamberRestLF6810_liveBCDEG_p8c2 A B C D E 0 G := by
    simp only [piQuarticChamberRestLF6810, piQuarticChamberRestLF6810_liveBCDEG_p8c1, piQuarticChamberRestLF6810_liveBCDEG_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF6810_liveBCDEG_p8c1_natDegree_lt A B C D E 0 G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF6810_liveBCDEG_p8c2_natDegree_lt A B C D E 0 G hdpos hd5 hd6 hd7 hd8 hd9)))

def piQuarticChamberRestLF6810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF6810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEFG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF6810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((15 / 16 : k) • (B * E * F))
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF6810_liveBCDEFG_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 2 * F.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd10 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : 2 * C.natDegree + G.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF6810 A B C D E F G).natDegree < d := by
  have hsplit : piQuarticChamberRestLF6810 A B C D E F G = piQuarticChamberRestLF6810_liveBCDEFG_p8c1 A B C D E F G + piQuarticChamberRestLF6810_liveBCDEFG_p8c2 A B C D E F G + piQuarticChamberRestLF6810_liveBCDEFG_p8c3 A B C D E F G := by
    simp only [piQuarticChamberRestLF6810, piQuarticChamberRestLF6810_liveBCDEFG_p8c1, piQuarticChamberRestLF6810_liveBCDEFG_p8c2, piQuarticChamberRestLF6810_liveBCDEFG_p8c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF6810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF6810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF6810_liveBCDEFG_p8c3_natDegree_lt A B C D E F G hdpos hd10 hd11 hd12 hd13 hd14)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF13810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF13810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEF_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF13810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEF_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : xiQuarticChamberRestLF13810 A B C D E F 0 = xiQuarticChamberRestLF13810_liveBCDEF_p8c1 A B C D E F 0 + xiQuarticChamberRestLF13810_liveBCDEF_p8c2 A B C D E F 0 := by
    simp only [xiQuarticChamberRestLF13810, xiQuarticChamberRestLF13810_liveBCDEF_p8c1, xiQuarticChamberRestLF13810_liveBCDEF_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF13810_liveBCDEF_p8c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3) (xiQuarticChamberRestLF13810_liveBCDEF_p8c2_natDegree_lt A B C D E F 0 hdpos hd4 hd5 hd6 hd7)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : E.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF13810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF13810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEFG_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF13810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF13810_liveBCDEFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF13810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : E.natDegree + G.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF13810 A B C D E F G).natDegree < d := by
  have hsplit : xiQuarticChamberRestLF13810 A B C D E F G = xiQuarticChamberRestLF13810_liveBCDEFG_p8c1 A B C D E F G + xiQuarticChamberRestLF13810_liveBCDEFG_p8c2 A B C D E F G := by
    simp only [xiQuarticChamberRestLF13810, xiQuarticChamberRestLF13810_liveBCDEFG_p8c1, xiQuarticChamberRestLF13810_liveBCDEFG_p8c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF13810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (xiQuarticChamberRestLF13810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8 hd9)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF14810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d)
    (hd4 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF14810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d)
    (hd3 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF14810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : C.natDegree + G.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d)
    (hd5 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF14810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd5 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF7810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF7810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDEF_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF7810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDEF_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : C.natDegree + 2 * E.natDegree < d)
    (hd10 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF7810 A B C D E F 0 = piQuarticChamberRestLF7810_liveBCDEF_p8c1 A B C D E F 0 + piQuarticChamberRestLF7810_liveBCDEF_p8c2 A B C D E F 0 := by
    simp only [piQuarticChamberRestLF7810, piQuarticChamberRestLF7810_liveBCDEF_p8c1, piQuarticChamberRestLF7810_liveBCDEF_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF7810_liveBCDEF_p8c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF7810_liveBCDEF_p8c2_natDegree_lt A B C D E F 0 hdpos hd6 hd7 hd8 hd9 hd10)))

def piQuarticChamberRestLF7810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF7810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : 3 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd7 : 2 * C.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd9 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF7810 A B C D 0 F G = piQuarticChamberRestLF7810_liveBCDFG_p8c1 A B C D 0 F G + piQuarticChamberRestLF7810_liveBCDFG_p8c2 A B C D 0 F G := by
    simp only [piQuarticChamberRestLF7810, piQuarticChamberRestLF7810_liveBCDFG_p8c1, piQuarticChamberRestLF7810_liveBCDFG_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF7810_liveBCDFG_p8c1_natDegree_lt A B C D 0 F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF7810_liveBCDFG_p8c2_natDegree_lt A B C D 0 F G hdpos hd5 hd6 hd7 hd8 hd9)))

def piQuarticChamberRestLF7810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 16 : k) • (A * B * D * E)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDEFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF7810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : B.natDegree + E.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDEFG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF7810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (C ^ 2 * G))
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + 2 * E.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF7810_liveBCDEFG_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd7 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd10 : 2 * C.natDegree + G.natDegree < d)
    (hd11 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + 2 * E.natDegree < d)
    (hd13 : 2 * D.natDegree + E.natDegree < d)
    (hd14 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF7810 A B C D E F G).natDegree < d := by
  have hsplit : piQuarticChamberRestLF7810 A B C D E F G = piQuarticChamberRestLF7810_liveBCDEFG_p8c1 A B C D E F G + piQuarticChamberRestLF7810_liveBCDEFG_p8c2 A B C D E F G + piQuarticChamberRestLF7810_liveBCDEFG_p8c3 A B C D E F G := by
    simp only [piQuarticChamberRestLF7810, piQuarticChamberRestLF7810_liveBCDEFG_p8c1, piQuarticChamberRestLF7810_liveBCDEFG_p8c2, piQuarticChamberRestLF7810_liveBCDEFG_p8c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF7810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF7810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF7810_liveBCDEFG_p8c3_natDegree_lt A B C D E F G hdpos hd10 hd11 hd12 hd13 hd14)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : C.natDegree + 2 * D.natDegree < d)
    (hd5 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF14810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF14810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (25 / 128 : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEF_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF14810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * D * E))
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEF_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd6 : 2 * C.natDegree + E.natDegree < d)
    (hd7 : C.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : xiQuarticChamberRestLF14810 A B C D E F 0 = xiQuarticChamberRestLF14810_liveBCDEF_p8c1 A B C D E F 0 + xiQuarticChamberRestLF14810_liveBCDEF_p8c2 A B C D E F 0 := by
    simp only [xiQuarticChamberRestLF14810, xiQuarticChamberRestLF14810_liveBCDEF_p8c1, xiQuarticChamberRestLF14810_liveBCDEF_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF14810_liveBCDEF_p8c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3 hd4) (xiQuarticChamberRestLF14810_liveBCDEF_p8c2_natDegree_lt A B C D E F 0 hdpos hd5 hd6 hd7 hd8)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF14810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF14810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEFG_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF14810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * D * E))
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : E.natDegree + G.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF14810_liveBCDEFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF14810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : E.natDegree + G.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF14810 A B C D E F G).natDegree < d := by
  have hsplit : xiQuarticChamberRestLF14810 A B C D E F G = xiQuarticChamberRestLF14810_liveBCDEFG_p8c1 A B C D E F G + xiQuarticChamberRestLF14810_liveBCDEFG_p8c2 A B C D E F G := by
    simp only [xiQuarticChamberRestLF14810, xiQuarticChamberRestLF14810_liveBCDEFG_p8c1, xiQuarticChamberRestLF14810_liveBCDEFG_p8c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF14810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (xiQuarticChamberRestLF14810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hCz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_CDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF15810_liveBCDEF_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEF_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEF_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEF_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF15810_liveBCDEF_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEF_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEF_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEF_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd7 : 2 * C.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : xiQuarticChamberRestLF15810 A B C D E F 0 = xiQuarticChamberRestLF15810_liveBCDEF_p8c1 A B C D E F 0 + xiQuarticChamberRestLF15810_liveBCDEF_p8c2 A B C D E F 0 := by
    simp only [xiQuarticChamberRestLF15810, xiQuarticChamberRestLF15810_liveBCDEF_p8c1, xiQuarticChamberRestLF15810_liveBCDEF_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF15810_liveBCDEF_p8c1_natDegree_lt A B C D E F 0 hdpos hd0 hd1 hd2 hd3 hd4) (xiQuarticChamberRestLF15810_liveBCDEF_p8c2_natDegree_lt A B C D E F 0 hdpos hd5 hd6 hd7 hd8 hd9)))

def xiQuarticChamberRestLF15810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF15810_liveBCDFG_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF15810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF15810_liveBCDFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : xiQuarticChamberRestLF15810 A B C D 0 F G = xiQuarticChamberRestLF15810_liveBCDFG_p8c1 A B C D 0 F G + xiQuarticChamberRestLF15810_liveBCDFG_p8c2 A B C D 0 F G := by
    simp only [xiQuarticChamberRestLF15810, xiQuarticChamberRestLF15810_liveBCDFG_p8c1, xiQuarticChamberRestLF15810_liveBCDFG_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF15810_liveBCDFG_p8c1_natDegree_lt A B C D 0 F G hdpos hd0 hd1 hd2 hd3) (xiQuarticChamberRestLF15810_liveBCDFG_p8c2_natDegree_lt A B C D 0 F G hdpos hd4 hd5 hd6 hd7)))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : E.natDegree + G.natDegree < d)
    (hd6 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : 2 * C.natDegree + E.natDegree < d)
    (hd1 : C.natDegree + 2 * D.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF15810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEFG_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF15810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((25 / 128 : k) • (B * C * F))
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF15810_liveBCDEFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * C.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : E.natDegree + G.natDegree < d)
    (hd11 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  have hsplit : xiQuarticChamberRestLF15810 A B C D E F G = xiQuarticChamberRestLF15810_liveBCDEFG_p8c1 A B C D E F G + xiQuarticChamberRestLF15810_liveBCDEFG_p8c2 A B C D E F G := by
    simp only [xiQuarticChamberRestLF15810, xiQuarticChamberRestLF15810_liveBCDEFG_p8c1, xiQuarticChamberRestLF15810_liveBCDEFG_p8c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF15810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (xiQuarticChamberRestLF15810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree < d)
    (hd1 : C.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + E.natDegree < d) :
    (kappaQuarticChamberRestLF9810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd5 : B.natDegree + D.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF8810_liveBCDEG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (45 / 64 : k) • (B ^ 2 * C * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDEG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF8810_liveBCDEG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 8 : k) • (B * D * G)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDEG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd8 : C.natDegree + 2 * E.natDegree < d)
    (hd9 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF8810 A B C D E 0 G = piQuarticChamberRestLF8810_liveBCDEG_p8c1 A B C D E 0 G + piQuarticChamberRestLF8810_liveBCDEG_p8c2 A B C D E 0 G := by
    simp only [piQuarticChamberRestLF8810, piQuarticChamberRestLF8810_liveBCDEG_p8c1, piQuarticChamberRestLF8810_liveBCDEG_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF8810_liveBCDEG_p8c1_natDegree_lt A B C D E 0 G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF8810_liveBCDEG_p8c2_natDegree_lt A B C D E 0 G hdpos hd5 hd6 hd7 hd8 hd9)))

def piQuarticChamberRestLF8810_liveBCDFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF8810_liveBCDFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (C * D * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd6 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + 2 * F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd9 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  have hsplit : piQuarticChamberRestLF8810 A B C D 0 F G = piQuarticChamberRestLF8810_liveBCDFG_p8c1 A B C D 0 F G + piQuarticChamberRestLF8810_liveBCDFG_p8c2 A B C D 0 F G := by
    simp only [piQuarticChamberRestLF8810, piQuarticChamberRestLF8810_liveBCDFG_p8c1, piQuarticChamberRestLF8810_liveBCDFG_p8c2, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF8810_liveBCDFG_p8c1_natDegree_lt A B C D 0 F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF8810_liveBCDFG_p8c2_natDegree_lt A B C D 0 F G hdpos hd5 hd6 hd7 hd8 hd9)))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 2 * F.natDegree < d)
    (hd5 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd6 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF8810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def piQuarticChamberRestLF8810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (A * B ^ 3 * D)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDEFG_p8c1]
  compute_degree
  omega

def piQuarticChamberRestLF8810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  - (5 / 16 : k) • (A * F ^ 2)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDEFG_p8c2]
  compute_degree
  omega

def piQuarticChamberRestLF8810_liveBCDEFG_p8c3
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 8 : k) • (B * D * G))
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_liveBCDEFG_p8c3_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810_liveBCDEFG_p8c3 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF8810_liveBCDEFG_p8c3]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF8810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + 2 * F.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd11 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF8810 A B C D E F G).natDegree < d := by
  have hsplit : piQuarticChamberRestLF8810 A B C D E F G = piQuarticChamberRestLF8810_liveBCDEFG_p8c1 A B C D E F G + piQuarticChamberRestLF8810_liveBCDEFG_p8c2 A B C D E F G + piQuarticChamberRestLF8810_liveBCDEFG_p8c3 A B C D E F G := by
    simp only [piQuarticChamberRestLF8810, piQuarticChamberRestLF8810_liveBCDEFG_p8c1, piQuarticChamberRestLF8810_liveBCDEFG_p8c2, piQuarticChamberRestLF8810_liveBCDEFG_p8c3, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (piQuarticChamberRestLF8810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (piQuarticChamberRestLF8810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8 hd9))) (piQuarticChamberRestLF8810_liveBCDEFG_p8c3_natDegree_lt A B C D E F G hdpos hd10 hd11 hd12 hd13 hd14)))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : C.natDegree + G.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF15810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * B.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + G.natDegree < d)
    (hd5 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF15810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF15810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF16810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCDEG
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
    (hd6 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF16810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 2 * B.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  subst hDz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF16810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

def xiQuarticChamberRestLF16810_liveBCDEFG_p8c1
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_liveBCDEFG_p8c1_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF16810_liveBCDEFG_p8c1 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF16810_liveBCDEFG_p8c1]
  compute_degree
  omega

def xiQuarticChamberRestLF16810_liveBCDEFG_p8c2
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 64 : k) • (B ^ 2 * G))
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_liveBCDEFG_p8c2_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810_liveBCDEFG_p8c2 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF16810_liveBCDEFG_p8c2]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF16810_natDegree_lt_of_live_BCDEFG
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
    (hd8 : C.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF16810 A B C D E F G).natDegree < d := by
  have hsplit : xiQuarticChamberRestLF16810 A B C D E F G = xiQuarticChamberRestLF16810_liveBCDEFG_p8c1 A B C D E F G + xiQuarticChamberRestLF16810_liveBCDEFG_p8c2 A B C D E F G := by
    simp only [xiQuarticChamberRestLF16810, xiQuarticChamberRestLF16810_liveBCDEFG_p8c1, xiQuarticChamberRestLF16810_liveBCDEFG_p8c2, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero]
    abel
  rw [hsplit]
  exact (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (xiQuarticChamberRestLF16810_liveBCDEFG_p8c1_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4) (xiQuarticChamberRestLF16810_liveBCDEFG_p8c2_natDegree_lt A B C D E F G hdpos hd5 hd6 hd7 hd8 hd9)))

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF10810_natDegree_lt_of_live_BCEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d) :
    (kappaQuarticChamberRestLF10810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF10810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega


end QuarticChamberFaces810

end Max11DegreeRoutes
