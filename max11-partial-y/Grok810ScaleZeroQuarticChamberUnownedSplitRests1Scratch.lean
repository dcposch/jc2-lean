import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberUnownedColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSplitPacketsScratch
import Grok810ScaleZeroQuarticChamberUnownedSplitColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns2Scratch

/-! # UnownedSplit chamber rests, part 1/1

26 of the 13 load-free and 13 full (packet,
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

section QuarticChamberUnownedSplitRests1810

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7000810_natDegree_lt_of_live_DG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF7000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest7000810_natDegree_lt_of_live_DG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (G.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d)) :
    (muQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF7000810_natDegree_lt_of_live_DG
      A B C D E F G hdpos hBz hCz hEz hFz
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | g0
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_DG l A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | g0
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_DG beta A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_DG gamma A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_DG delta A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_DG zeta A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7000810_natDegree_lt_of_live_DG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF7000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest7000810_natDegree_lt_of_live_DG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (3 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (G.natDegree < d)) :
    (piQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF7000810_natDegree_lt_of_live_DG
      A B C D E F G hdpos hBz hCz hEz hFz
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | g0
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_DG l A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_DG gamma A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_DG epsilon A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_DG eta A B C D E F G hdpos hBz hCz hEz hFz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7001810_natDegree_lt_of_live_EF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0) :
    (muQuarticChamberRestLF7001810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF7001810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest7001810_natDegree_lt_of_live_EF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (2 * A.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d)) :
    (muQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF7001810_natDegree_lt_of_live_EF
      A B C D E F G hdpos hBz hCz hDz hGz
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | g0
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_EF l A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | g0
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_EF beta A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_EF delta A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_EF epsilon A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest7001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7000810_natDegree_lt_of_live_EF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0) :
    (xiQuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF7000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest7000810_natDegree_lt_of_live_EF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (3 * A.natDegree + F.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (F.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d)) :
    (xiQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF7000810_natDegree_lt_of_live_EF
      A B C D E F G hdpos hBz hCz hDz hGz
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_EF l A B C D E F G hdpos hBz hCz hDz hGz g0 g1
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | g0
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_EF beta A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_EF delta A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_EF zeta A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_EF eta A B C D E F G hdpos hBz hCz hDz hGz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [xiQuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7001810_natDegree_lt_of_live_EG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (xiQuarticChamberRestLF7001810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF7001810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest7001810_natDegree_lt_of_live_EG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hbepsilon : epsilon = 0 ∨ (G.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d)) :
    (xiQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF7001810_natDegree_lt_of_live_EG
      A B C D E F G hdpos hBz hCz hDz hFz
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_EG epsilon A B C D E F G hdpos hBz hCz hDz hFz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_EG eta A B C D E F G hdpos hBz hCz hDz hFz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [xiQuarticChamberRest7001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7001810_natDegree_lt_of_live_EG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF7001810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF7001810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest7001810_natDegree_lt_of_live_EG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hbgamma : gamma = 0 ∨ (G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d)) :
    (muQuarticChamberRest7001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF7001810_natDegree_lt_of_live_EG
      A B C D E F G hdpos hBz hCz hDz hFz
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_EG gamma A B C D E F G hdpos hBz hCz hDz hFz g0
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_EG epsilon A B C D E F G hdpos hBz hCz hDz hFz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest7001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF7000810_natDegree_lt_of_live_EG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF7000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest7000810_natDegree_lt_of_live_EG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hFz : F = 0)
    (hbgamma : gamma = 0 ∨ (2 * E.natDegree < d))
    (hbeta : eta = 0 ∨ (G.natDegree < d)) :
    (piQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF7000810_natDegree_lt_of_live_EG
      A B C D E F G hdpos hBz hCz hDz hFz
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnL1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_EG gamma A B C D E F G hdpos hBz hCz hDz hFz g0
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_EG eta A B C D E F G hdpos hBz hCz hDz hFz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [piQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [piQuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF7002810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hd0 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF7002810 A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRestLF7002810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest7002810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hl0 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest7002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF7002810_natDegree_lt_of_live_DEF
      A B C D E F G hdpos hBz hCz hGz hl0
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_DEF l A B C D E F G hdpos hBz hCz hGz g0 g1 g2 g3
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_DEF beta A B C D E F G hdpos hBz hCz hGz g0 g1 g2
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_DEF gamma A B C D E F G hdpos hBz hCz hGz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_DEF delta A B C D E F G hdpos hBz hCz hGz g0 g1
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [xiQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_DEF zeta A B C D E F G hdpos hBz hCz hGz g0 g1
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_DEF eta A B C D E F G hdpos hBz hCz hGz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_DEF theta A B C D E F G hdpos hBz hCz hGz g0
  simp only [xiQuarticChamberRest7002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF7000810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF7000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest7000810_natDegree_lt_of_live_DEF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF7000810_natDegree_lt_of_live_DEF
      A B C D E F G hdpos hBz hCz hGz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_DEF l A B C D E F G hdpos hBz hCz hGz g0 g1 g2
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_DEF beta A B C D E F G hdpos hBz hCz hGz g0 g1
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_DEF gamma A B C D E F G hdpos hBz hCz hGz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_DEF delta A B C D E F G hdpos hBz hCz hGz g0 g1
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_DEF epsilon A B C D E F G hdpos hBz hCz hGz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_DEF zeta A B C D E F G hdpos hBz hCz hGz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
    simp only [kappaQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_DEF theta A B C D E F G hdpos hBz hCz hGz g0
  simp only [kappaQuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7002810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF7002810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF7002810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest7002810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hl0 : A.natDegree + 2 * D.natDegree < d)
    (hl1 : 3 * C.natDegree < d)
    (hl2 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d)) :
    (muQuarticChamberRest7002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF7002810_natDegree_lt_of_live_CDFG
      A B C D E F G hdpos hBz hEz hl0 hl1 hl2
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_CDFG l A B C D E F G hdpos hBz hEz g0 g1 g2 g3
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_CDFG beta A B C D E F G hdpos hBz hEz g0 g1 g2
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_CDFG gamma A B C D E F G hdpos hBz hEz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_CDFG delta A B C D E F G hdpos hBz hEz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hBz
    subst hEz
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
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_CDFG zeta A B C D E F G hdpos hBz hEz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_CDFG eta A B C D E F G hdpos hBz hEz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest7002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRestLF7000810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hd0 : 2 * C.natDegree + D.natDegree < d) :
    (n2QuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticChamberRestLF7000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRest7000810_natDegree_lt_of_live_CDFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hEz : E = 0)
    (hl0 : 2 * C.natDegree + D.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d))
    (hbeta : eta = 0 ∨ (D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (n2QuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n2QuarticChamberRestLF7000810_natDegree_lt_of_live_CDFG
      A B C D E F G hdpos hBz hEz hl0
  have hc0 : (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n2QuarticColumnL810_zero]
      simpa using hdpos
    · exact n2QuarticColumnL810_natDegree_lt_of_live_CDFG l A B C D E F G hdpos hBz hEz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n2QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnBeta810_natDegree_lt_of_live_CDFG beta A B C D E F G hdpos hBz hEz g0 g1 g2 g3 g4
  have hc2 : (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [n2QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n2QuarticColumnGamma810_natDegree_lt_of_live_CDFG gamma A B C D E F G hdpos hBz hEz g0
  have hc3 : (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n2QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnDelta810_natDegree_lt_of_live_CDFG delta A B C D E F G hdpos hBz hEz g0 g1 g2 g3
  have hc4 : (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n2QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEpsilon810_natDegree_lt_of_live_CDFG epsilon A B C D E F G hdpos hBz hEz g0
  have hc5 : (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnZeta810_natDegree_lt_of_live_CDFG zeta A B C D E F G hdpos hBz hEz g0 g1
  have hc6 : (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n2QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEta810_natDegree_lt_of_live_CDFG eta A B C D E F G hdpos hBz hEz g0
  have hc7 : (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnTheta810_natDegree_lt_of_live_CDFG theta A B C D E F G hdpos hBz hEz g0 g1
  simp only [n2QuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF7002810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree < d)
    (hd2 : D.natDegree + F.natDegree < d)
    (hd3 : 2 * E.natDegree < d) :
    (muQuarticChamberRestLF7002810 A B C D E F G).natDegree < d := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF7002810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest7002810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hl0 : A.natDegree + 2 * D.natDegree < d)
    (hl1 : 3 * C.natDegree < d)
    (hl2 : D.natDegree + F.natDegree < d)
    (hl3 : 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d)) :
    (muQuarticChamberRest7002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF7002810_natDegree_lt_of_live_CDEFG
      A B C D E F G hdpos hBz hl0 hl1 hl2 hl3
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_CDEFG l A B C D E F G hdpos hBz g0 g1 g2 g3 g4
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_CDEFG beta A B C D E F G hdpos hBz g0 g1 g2
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_CDEFG gamma A B C D E F G hdpos hBz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_CDEFG delta A B C D E F G hdpos hBz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG epsilon A B C D E F G hdpos hBz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_CDEFG zeta A B C D E F G hdpos hBz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_CDEFG eta A B C D E F G hdpos hBz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest7002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `n6QuarticChamberRestLF7000810` on the live set `CDEFG` (6 monomials). -/
def n6QuarticChamberRestLF7000810PartCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 96 : k) • (A * C ^ 2 * F)
  + (95 / 384 : k) • (A * C * D * E)
  + (25 / 384 : k) • (A * D ^ 3)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRestLF7000810PartCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + 3 * D.natDegree < d)
    (hd3 : 3 * C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree + F.natDegree < d) :
    (n6QuarticChamberRestLF7000810PartCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [n6QuarticChamberRestLF7000810PartCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `n6QuarticChamberRestLF7000810` on the live set `CDEFG` (2 monomials). -/
def n6QuarticChamberRestLF7000810PartCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRestLF7000810PartCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree + F.natDegree < d)
    (hd1 : D.natDegree + 2 * E.natDegree < d) :
    (n6QuarticChamberRestLF7000810PartCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [n6QuarticChamberRestLF7000810PartCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRestLF7000810_split_of_live_CDEFG
    (A B C D E F G : k[X])
    (hBz : B = 0) :
    n6QuarticChamberRestLF7000810 A B C D E F G =
      n6QuarticChamberRestLF7000810PartCDEFG1810 A B C D E F G +
        n6QuarticChamberRestLF7000810PartCDEFG2810 A B C D E F G := by
  subst hBz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticChamberRestLF7000810, n6QuarticChamberRestLF7000810PartCDEFG1810, n6QuarticChamberRestLF7000810PartCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRestLF7000810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hd0 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + 3 * D.natDegree < d)
    (hd3 : 3 * C.natDegree + D.natDegree < d)
    (hd4 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd6 : 2 * D.natDegree + F.natDegree < d)
    (hd7 : D.natDegree + 2 * E.natDegree < d) :
    (n6QuarticChamberRestLF7000810 A B C D E F G).natDegree < d := by
  rw [n6QuarticChamberRestLF7000810_split_of_live_CDEFG A B C D E F G hBz]
  exact natDegree_add_lt810 (n6QuarticChamberRestLF7000810PartCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n6QuarticChamberRestLF7000810PartCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7)

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRest7000810_natDegree_lt_of_live_CDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hl0 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hl1 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl2 : A.natDegree + 3 * D.natDegree < d)
    (hl3 : 3 * C.natDegree + D.natDegree < d)
    (hl4 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl5 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl6 : 2 * D.natDegree + F.natDegree < d)
    (hl7 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + E.natDegree + G.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + C.natDegree + D.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n6QuarticChamberRest7000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n6QuarticChamberRestLF7000810_natDegree_lt_of_live_CDEFG
      A B C D E F G hdpos hBz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
  have hc0 : (n6QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20⟩
    · rw [n6QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n6QuarticColumnL1810_natDegree_lt_of_live_CDEFG l A B C D E F G hdpos hBz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (n6QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20⟩
    · rw [n6QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n6QuarticColumnL2810_natDegree_lt_of_live_CDEFG l A B C D E F G hdpos hBz g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
  have hc2 : (n6QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [n6QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n6QuarticColumnBeta1810_natDegree_lt_of_live_CDEFG beta A B C D E F G hdpos hBz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc3 : (n6QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [n6QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n6QuarticColumnBeta2810_natDegree_lt_of_live_CDEFG beta A B C D E F G hdpos hBz g9 g10 g11
  have hc4 : (n6QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n6QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n6QuarticColumnGamma810_natDegree_lt_of_live_CDEFG gamma A B C D E F G hdpos hBz g0 g1 g2 g3
  have hc5 : (n6QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n6QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnDelta810_natDegree_lt_of_live_CDEFG delta A B C D E F G hdpos hBz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc6 : (n6QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [n6QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n6QuarticColumnEpsilon810_natDegree_lt_of_live_CDEFG epsilon A B C D E F G hdpos hBz g0 g1 g2
  have hc7 : (n6QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n6QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnZeta810_natDegree_lt_of_live_CDEFG zeta A B C D E F G hdpos hBz g0 g1 g2 g3 g4 g5 g6
  have hc8 : (n6QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n6QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnEta810_natDegree_lt_of_live_CDEFG eta A B C D E F G hdpos hBz g0 g1
  have hc9 : (n6QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n6QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnTheta810_natDegree_lt_of_live_CDEFG theta A B C D E F G hdpos hBz g0 g1 g2 g3 g4
  simp only [n6QuarticChamberRest7000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9


end QuarticChamberUnownedSplitRests1810

end Max11DegreeRoutes
