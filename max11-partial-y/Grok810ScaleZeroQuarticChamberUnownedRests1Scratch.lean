import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedPacketsScratch
import Grok810ScaleZeroQuarticChamberUnownedColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns1Scratch

/-! # Unowned chamber rests, part 1/4

39 of the 75 load-free and 75 full (packet,
live-set) rest bounds the kills need.  Independent of its
siblings.  Untracked working note.
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

section QuarticChamberUnownedRests1810

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF5000810_natDegree_lt_of_live_C
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF5000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest5000810_natDegree_lt_of_live_C
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hbgamma : gamma = 0 ∨ (2 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d)) :
    (muQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF5000810_natDegree_lt_of_live_C
      A B C D E F G hdpos hBz hDz hEz hFz hGz
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_C gamma A B C D E F G hdpos hBz hDz hEz hFz hGz g0
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_C eta A B C D E F G hdpos hBz hDz hEz hFz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF5001810_natDegree_lt_of_live_E
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hDz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF5001810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest5001810_natDegree_lt_of_live_E
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d)) :
    (muQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF5001810_natDegree_lt_of_live_E
      A B C D E F G hdpos hBz hCz hDz hFz hGz
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_E epsilon A B C D E F G hdpos hBz hCz hDz hFz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5000810_natDegree_lt_of_live_G
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
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
  simp only [piQuarticChamberRestLF5000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest5000810_natDegree_lt_of_live_G
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbeta : eta = 0 ∨ (G.natDegree < d)) :
    (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5000810_natDegree_lt_of_live_G
      A B C D E F G hdpos hBz hCz hDz hEz hFz
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_G eta A B C D E F G hdpos hBz hCz hDz hEz hFz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n3QuarticChamberRestLF5000810` (18 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedRests1_n3QuarticChamberRestLF5000810
    (A B C D E F G : k[X]) :
    n3QuarticChamberRestLF5000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 8192) : k), (-(175 / 8192) : k), (-(21 / 4096) : k),
      (65 / 2048 : k), (45 / 1024 : k), (85 / 2048 : k),
      (5 / 128 : k), (135 / 1024 : k), (45 / 1024 : k),
      (-(15 / 256) : k), (-(15 / 256) : k), (-(15 / 128) : k),
      (-(5 / 32) : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(5 / 128) : k), (5 / 16 : k)
      ]
      [
      [2, 2, 0, 1, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0],
      [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1]
      ] := by
  simp only [n3QuarticChamberRestLF5000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : 3 * D.natDegree < d) :
    (n3QuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
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
  rw [refl810PolyOf_ChamberUnownedRests1_n3QuarticChamberRestLF5000810]
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
theorem n3QuarticChamberRest5000810_natDegree_lt_of_live_CD
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : 3 * D.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ 2 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d)) :
    (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CD
      A B C D E F G hdpos hBz hEz hFz hGz hl0
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_CD l A B C D E F G hdpos hBz hEz hFz hGz g0 g1 g2 g3 g4
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_CD l A B C D E F G hdpos hBz hEz hFz hGz g5
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_CD beta A B C D E F G hdpos hBz hEz hFz hGz g0 g1 g2 g3 g4
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_CD gamma A B C D E F G hdpos hBz hEz hFz hGz g0
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_CD delta A B C D E F G hdpos hBz hEz hFz hGz g0 g1 g2 g3
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_CD epsilon A B C D E F G hdpos hBz hEz hFz hGz g0
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_CD zeta A B C D E F G hdpos hBz hEz hFz hGz g0 g1 g2
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_CD eta A B C D E F G hdpos hBz hEz hFz hGz g0
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_CD theta A B C D E F G hdpos hBz hEz hFz hGz g0 g1
  simp only [n3QuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5000810_natDegree_lt_of_live_CE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF5000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest5000810_natDegree_lt_of_live_CE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hbgamma : gamma = 0 ∨ (C.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d)) :
    (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF5000810_natDegree_lt_of_live_CE
      A B C D E F G hdpos hBz hDz hFz hGz
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    subst hBz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    subst hBz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_CE gamma A B C D E F G hdpos hBz hDz hFz hGz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    subst hBz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_CE epsilon A B C D E F G hdpos hBz hDz hFz hGz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    subst hBz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_CE eta A B C D E F G hdpos hBz hDz hFz hGz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hDz
    subst hFz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [xiQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5001810` (20 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5001810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5001810 A B C D E F G =
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
  simp only [piQuarticChamberRestLF5001810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5001810_natDegree_lt_of_live_CF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * C.natDegree < d) :
    (piQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
  subst hBz
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
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5001810]
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
theorem piQuarticChamberRest5001810_natDegree_lt_of_live_CF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 4 * C.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5001810_natDegree_lt_of_live_CF
      A B C D E F G hdpos hBz hDz hEz hGz hl0
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_CF l A B C D E F G hdpos hBz hDz hEz hGz g0 g1
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_CF l A B C D E F G hdpos hBz hDz hEz hGz g2
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_CF beta A B C D E F G hdpos hBz hDz hEz hGz g0 g1
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_CF gamma A B C D E F G hdpos hBz hDz hEz hGz g0
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_CF delta A B C D E F G hdpos hBz hDz hEz hGz g0 g1
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hBz
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
    omega
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_CF zeta A B C D E F G hdpos hBz hDz hEz hGz g0
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_CF eta A B C D E F G hdpos hBz hDz hEz hGz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_CF theta A B C D E F G hdpos hBz hDz hEz hGz g0
  simp only [piQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF5000810` (20 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5000810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF5000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (15 / 256 : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (-(15 / 16) : k), (-(5 / 16) : k), (-(15 / 16) : k),
      (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF5000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5000810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * C.natDegree < d)
    (hd1 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
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
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5000810]
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
theorem piQuarticChamberRest5000810_natDegree_lt_of_live_CG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 4 * C.natDegree < d)
    (hl1 : 2 * C.natDegree + G.natDegree < d)
    (hbgamma : gamma = 0 ∨ (3 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * C.natDegree < d ∧ G.natDegree < d)) :
    (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5000810_natDegree_lt_of_live_CG
      A B C D E F G hdpos hBz hDz hEz hFz hl0 hl1
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_CG gamma A B C D E F G hdpos hBz hDz hEz hFz g0
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_CG eta A B C D E F G hdpos hBz hDz hEz hFz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
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
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5001810_natDegree_lt_of_live_FG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * G.natDegree < d) :
    (piQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5001810]
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
theorem piQuarticChamberRest5001810_natDegree_lt_of_live_FG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : 2 * G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + F.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (G.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5001810_natDegree_lt_of_live_FG
      A B C D E F G hdpos hBz hCz hDz hEz hl0
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_FG l A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_FG l A B C D E F G hdpos hBz hCz hDz hEz g1
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | g0
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_FG beta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [piQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_FG delta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hDz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_FG zeta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_FG eta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_FG theta A B C D E F G hdpos hBz hCz hDz hEz g0
  simp only [piQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n2QuarticChamberRestLF5000810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedRests1_n2QuarticChamberRestLF5000810
    (A B C D E F G : k[X]) :
    n2QuarticChamberRestLF5000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 512 : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k)
      ]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [n2QuarticChamberRestLF5000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRestLF5000810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d)
    (hd2 : B.natDegree + 2 * D.natDegree < d) :
    (n2QuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedRests1_n2QuarticChamberRestLF5000810]
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
theorem n2QuarticChamberRest5000810_natDegree_lt_of_live_BCD
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hEz : E = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : 3 * B.natDegree + C.natDegree < d)
    (hl2 : B.natDegree + 2 * D.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * B.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (n2QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n2QuarticChamberRestLF5000810_natDegree_lt_of_live_BCD
      A B C D E F G hdpos hEz hFz hGz hl0 hl1 hl2
  have hc0 : (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n2QuarticColumnL810_zero]
      simpa using hdpos
    · exact n2QuarticColumnL810_natDegree_lt_of_live_BCD l A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n2QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnBeta810_natDegree_lt_of_live_BCD beta A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4 g5 g6
  have hc2 : (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n2QuarticColumnGamma810_natDegree_lt_of_live_BCD gamma A B C D E F G hdpos hEz hFz hGz g0 g1
  have hc3 : (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n2QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnDelta810_natDegree_lt_of_live_BCD delta A B C D E F G hdpos hEz hFz hGz g0 g1 g2 g3 g4
  have hc4 : (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n2QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEpsilon810_natDegree_lt_of_live_BCD epsilon A B C D E F G hdpos hEz hFz hGz g0
  have hc5 : (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [n2QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnZeta810_natDegree_lt_of_live_BCD zeta A B C D E F G hdpos hEz hFz hGz g0 g1 g2
  have hc6 : (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n2QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEta810_natDegree_lt_of_live_BCD eta A B C D E F G hdpos hEz hFz hGz g0
  have hc7 : (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnTheta810_natDegree_lt_of_live_BCD theta A B C D E F G hdpos hEz hFz hGz g0 g1
  simp only [n2QuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5001810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedRests1_xiQuarticChamberRestLF5001810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5001810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(25 / 128) : k), (-(15 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5001810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5001810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedRests1_xiQuarticChamberRestLF5001810]
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
theorem xiQuarticChamberRest5001810_natDegree_lt_of_live_BDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : A.natDegree + 4 * B.natDegree < d)
    (hl1 : 3 * B.natDegree + D.natDegree < d)
    (hl2 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ 2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF5001810_natDegree_lt_of_live_BDF
      A B C D E F G hdpos hCz hEz hGz hl0 hl1 hl2
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_BDF l A B C D E F G hdpos hCz hEz hGz g0 g1 g2 g3 g4 g5
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_BDF beta A B C D E F G hdpos hCz hEz hGz g0 g1 g2 g3
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_BDF gamma A B C D E F G hdpos hCz hEz hGz g0 g1 g2
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_BDF delta A B C D E F G hdpos hCz hEz hGz g0 g1 g2
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_BDF epsilon A B C D E F G hdpos hCz hEz hGz g0 g1
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_BDF zeta A B C D E F G hdpos hCz hEz hGz g0 g1
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_BDF eta A B C D E F G hdpos hCz hEz hGz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_BDF theta A B C D E F G hdpos hCz hEz hGz g0
  simp only [xiQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5001810_natDegree_lt_of_live_BEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + E.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5001810]
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
theorem piQuarticChamberRest5001810_natDegree_lt_of_live_BEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hl1 : 3 * B.natDegree + F.natDegree < d)
    (hl2 : B.natDegree + E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 5 * B.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5001810_natDegree_lt_of_live_BEF
      A B C D E F G hdpos hCz hDz hGz hl0 hl1 hl2
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BEF l A B C D E F G hdpos hCz hDz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BEF l A B C D E F G hdpos hCz hDz hGz g7
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BEF beta A B C D E F G hdpos hCz hDz hGz g0 g1 g2 g3 g4
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BEF gamma A B C D E F G hdpos hCz hDz hGz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BEF delta A B C D E F G hdpos hCz hDz hGz g0 g1 g2
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BEF epsilon A B C D E F G hdpos hCz hDz hGz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BEF zeta A B C D E F G hdpos hCz hDz hGz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BEF eta A B C D E F G hdpos hCz hDz hGz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BEF theta A B C D E F G hdpos hCz hDz hGz g0
  simp only [piQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 3 * D.natDegree < d) :
    (n3QuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_n3QuarticChamberRestLF5000810]
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
theorem n3QuarticChamberRest5000810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl1 : 3 * D.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ E.natDegree < d)) :
    (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CDE
      A B C D E F G hdpos hBz hFz hGz hl0 hl1
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_CDE l A B C D E F G hdpos hBz hFz hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_CDE l A B C D E F G hdpos hBz hFz hGz g8 g9
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_CDE beta A B C D E F G hdpos hBz hFz hGz g0 g1 g2 g3 g4 g5 g6 g7
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_CDE gamma A B C D E F G hdpos hBz hFz hGz g0 g1
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_CDE delta A B C D E F G hdpos hBz hFz hGz g0 g1 g2 g3 g4
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_CDE epsilon A B C D E F G hdpos hBz hFz hGz g0
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_CDE zeta A B C D E F G hdpos hBz hFz hGz g0 g1 g2 g3
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_CDE eta A B C D E F G hdpos hBz hFz hGz g0
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_CDE theta A B C D E F G hdpos hBz hFz hGz g0 g1 g2
  simp only [n3QuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF5000810` (12 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedRests1_xiQuarticChamberRestLF5000810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF5000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (15 / 256 : k),
      (55 / 1024 : k), (45 / 512 : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(25 / 128) : k),
      (-(15 / 128) : k), (5 / 16 : k), (5 / 32 : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF5000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5000810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hd0 : C.natDegree + 2 * D.natDegree < d) :
    (xiQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hFz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_xiQuarticChamberRestLF5000810]
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
theorem xiQuarticChamberRest5000810_natDegree_lt_of_live_CDE
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hFz : F = 0)
    (hGz : G = 0)
    (hl0 : C.natDegree + 2 * D.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * C.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF5000810_natDegree_lt_of_live_CDE
      A B C D E F G hdpos hBz hFz hGz hl0
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_CDE l A B C D E F G hdpos hBz hFz hGz g0 g1 g2 g3
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_CDE beta A B C D E F G hdpos hBz hFz hGz g0 g1 g2
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_CDE gamma A B C D E F G hdpos hBz hFz hGz g0 g1
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_CDE delta A B C D E F G hdpos hBz hFz hGz g0 g1
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_CDE epsilon A B C D E F G hdpos hBz hFz hGz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_CDE zeta A B C D E F G hdpos hBz hFz hGz g0
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_CDE eta A B C D E F G hdpos hBz hFz hGz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_CDE theta A B C D E F G hdpos hBz hFz hGz g0
  simp only [xiQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5001810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5001810]
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
theorem piQuarticChamberRest5001810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl1 : 4 * C.natDegree < d)
    (hl2 : C.natDegree + D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5001810_natDegree_lt_of_live_CDF
      A B C D E F G hdpos hBz hEz hGz hl0 hl1 hl2
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_CDF l A B C D E F G hdpos hBz hEz hGz g0 g1 g2 g3
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_CDF l A B C D E F G hdpos hBz hEz hGz g4 g5
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_CDF beta A B C D E F G hdpos hBz hEz hGz g0 g1 g2 g3
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_CDF gamma A B C D E F G hdpos hBz hEz hGz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_CDF delta A B C D E F G hdpos hBz hEz hGz g0 g1 g2
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_CDF epsilon A B C D E F G hdpos hBz hEz hGz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_CDF zeta A B C D E F G hdpos hBz hEz hGz g0 g1
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_CDF eta A B C D E F G hdpos hBz hEz hGz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_CDF theta A B C D E F G hdpos hBz hEz hGz g0
  simp only [piQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * C.natDegree + F.natDegree < d)
    (hd1 : 3 * D.natDegree < d) :
    (n3QuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedRests1_n3QuarticChamberRestLF5000810]
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
theorem n3QuarticChamberRest5000810_natDegree_lt_of_live_CDF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 2 * C.natDegree + F.natDegree < d)
    (hl1 : 3 * D.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ 2 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d)) :
    (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CDF
      A B C D E F G hdpos hBz hEz hGz hl0 hl1
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_CDF l A B C D E F G hdpos hBz hEz hGz g0 g1 g2 g3 g4 g5
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_CDF l A B C D E F G hdpos hBz hEz hGz g6 g7
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_CDF beta A B C D E F G hdpos hBz hEz hGz g0 g1 g2 g3 g4 g5
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_CDF gamma A B C D E F G hdpos hBz hEz hGz g0 g1
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_CDF delta A B C D E F G hdpos hBz hEz hGz g0 g1 g2 g3
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_CDF epsilon A B C D E F G hdpos hBz hEz hGz g0 g1
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_CDF zeta A B C D E F G hdpos hBz hEz hGz g0 g1 g2
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_CDF eta A B C D E F G hdpos hBz hEz hGz g0 g1
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_CDF theta A B C D E F G hdpos hBz hEz hGz g0 g1
  simp only [n3QuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5000810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 4 * C.natDegree < d)
    (hd2 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5000810]
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
theorem piQuarticChamberRest5000810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl1 : 4 * C.natDegree < d)
    (hl2 : 2 * C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 3 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * C.natDegree < d ∧ G.natDegree < d)) :
    (piQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5000810_natDegree_lt_of_live_CDG
      A B C D E F G hdpos hBz hEz hFz hl0 hl1 hl2
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_CDG l A B C D E F G hdpos hBz hEz hFz g0 g1
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_CDG l A B C D E F G hdpos hBz hEz hFz g2
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_CDG beta A B C D E F G hdpos hBz hEz hFz g0 g1
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_CDG gamma A B C D E F G hdpos hBz hEz hFz g0 g1
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_CDG delta A B C D E F G hdpos hBz hEz hFz g0
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_CDG epsilon A B C D E F G hdpos hBz hEz hFz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_CDG zeta A B C D E F G hdpos hBz hEz hFz g0
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_CDG eta A B C D E F G hdpos hBz hEz hFz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hEz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + D.natDegree + G.natDegree < d)
    (hd1 : 3 * D.natDegree < d) :
    (n3QuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_n3QuarticChamberRestLF5000810]
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
theorem n3QuarticChamberRest5000810_natDegree_lt_of_live_CDG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + D.natDegree + G.natDegree < d)
    (hl1 : 3 * D.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d)) :
    (n3QuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF5000810_natDegree_lt_of_live_CDG
      A B C D E F G hdpos hBz hEz hFz hl0 hl1
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_CDG l A B C D E F G hdpos hBz hEz hFz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_CDG l A B C D E F G hdpos hBz hEz hFz g7
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_CDG beta A B C D E F G hdpos hBz hEz hFz g0 g1 g2 g3 g4
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_CDG gamma A B C D E F G hdpos hBz hEz hFz g0
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_CDG delta A B C D E F G hdpos hBz hEz hFz g0 g1 g2 g3 g4
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_CDG epsilon A B C D E F G hdpos hBz hEz hFz g0
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_CDG zeta A B C D E F G hdpos hBz hEz hFz g0 g1 g2 g3
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_CDG eta A B C D E F G hdpos hBz hEz hFz g0
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_CDG theta A B C D E F G hdpos hBz hEz hFz g0 g1
  simp only [n3QuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5001810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 4 * C.natDegree < d)
    (hd1 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF5001810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5001810]
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
theorem piQuarticChamberRest5001810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : 4 * C.natDegree < d)
    (hl1 : C.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * C.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (C.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest5001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF5001810_natDegree_lt_of_live_CEF
      A B C D E F G hdpos hBz hDz hGz hl0 hl1
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_CEF l A B C D E F G hdpos hBz hDz hGz g0 g1 g2
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_CEF l A B C D E F G hdpos hBz hDz hGz g3
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_CEF beta A B C D E F G hdpos hBz hDz hGz g0 g1 g2
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_CEF gamma A B C D E F G hdpos hBz hDz hGz g0 g1
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_CEF delta A B C D E F G hdpos hBz hDz hGz g0 g1
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_CEF epsilon A B C D E F G hdpos hBz hDz hGz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_CEF zeta A B C D E F G hdpos hBz hDz hGz g0
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_CEF eta A B C D E F G hdpos hBz hDz hGz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_CEF theta A B C D E F G hdpos hBz hDz hGz g0
  simp only [piQuarticChamberRest5001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF5000810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hd0 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hGz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedRests1_xiQuarticChamberRestLF5000810]
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
theorem xiQuarticChamberRest5000810_natDegree_lt_of_live_CEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hl0 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (C.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * C.natDegree < d))
    (hbzeta : zeta = 0 ∨ (F.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d)) :
    (xiQuarticChamberRest5000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF5000810_natDegree_lt_of_live_CEF
      A B C D E F G hdpos hBz hDz hGz hl0
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_CEF l A B C D E F G hdpos hBz hDz hGz g0 g1 g2
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_CEF beta A B C D E F G hdpos hBz hDz hGz g0 g1
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_CEF gamma A B C D E F G hdpos hBz hDz hGz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_CEF delta A B C D E F G hdpos hBz hDz hGz g0
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_CEF epsilon A B C D E F G hdpos hBz hDz hGz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_CEF zeta A B C D E F G hdpos hBz hDz hGz g0
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_CEF eta A B C D E F G hdpos hBz hDz hGz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hDz
    subst hGz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [xiQuarticChamberRest5000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF5000810_natDegree_lt_of_live_CEG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hd0 : 4 * C.natDegree < d)
    (hd1 : 2 * C.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + 2 * E.natDegree < d) :
    (piQuarticChamberRestLF5000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedRests1_piQuarticChamberRestLF5000810]
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


end QuarticChamberUnownedRests1810

end Max11DegreeRoutes
