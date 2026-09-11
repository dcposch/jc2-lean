import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberUnownedRefineColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeColumns1Scratch

/-! # Tied load columns, `(8,10)` scale zero

6 tied tops: the load column's top terms as their own
polynomial, the column and the combined rest without them, the two
split identities, the rest bound and the top's `coeff` value.  This
is what a load kill and a tied-load system row need on top of the
ordinary face packets.  Untracked working note.
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

section QuarticChamberUnownedTreePieces810

set_option maxHeartbeats 64000000 in
/-- The tied top of the `epsilon` column of `N₄` (1 monomial, degree `2 * A.natDegree + F.natDegree`). -/
def n4QuarticColumnTop1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • (A ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- That column without its tied top (8 monomials). -/
def n4QuarticColumnEpsilonOff1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 64 * epsilon : k)) • (A ^ 2 * B * C)
  - (1 / 16 * epsilon : k) • (A * B ^ 3)
  + (1 / 4 * epsilon : k) • (A * B * E)
  + (1 / 4 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_split1
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810 epsilon A B C D E F G =
      n4QuarticColumnTop1810 epsilon A B C D E F G + n4QuarticColumnEpsilonOff1810 epsilon A B C D E F G := by
  simp only [n4QuarticColumnEpsilon810, n4QuarticColumnTop1810, n4QuarticColumnEpsilonOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRestOff1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9500810 A B C D E F G +
    n4QuarticColumnL1810 l A B C D E F G +
    n4QuarticColumnL2810 l A B C D E F G +
    n4QuarticColumnBeta1810 beta A B C D E F G +
    n4QuarticColumnBeta2810 beta A B C D E F G +
    n4QuarticColumnGamma810 gamma A B C D E F G +
    n4QuarticColumnDelta810 delta A B C D E F G +
    n4QuarticColumnZeta810 zeta A B C D E F G +
    n4QuarticColumnEta810 eta A B C D E F G +
    n4QuarticColumnTheta810 theta A B C D E F G +
    n4QuarticColumnEpsilonOff1810 epsilon A B C D E F G

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRest9500810_split1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n4QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticColumnTop1810 epsilon A B C D E F G +
        n4QuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n4QuarticChamberRest9500810, n4QuarticChamberRestOff1810, n4QuarticColumnEpsilon810, n4QuarticColumnTop1810, n4QuarticColumnEpsilonOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnTop1810_coeff
    (epsilon : k)
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hFne : F ≠ 0) :
    (n4QuarticColumnTop1810 epsilon A B C D E F G).coeff (2 * A.natDegree + F.natDegree) =
      (1 / 32 : k) * epsilon * (A.leadingCoeff ^ 2 * F.leadingCoeff) := by
  simp only [n4QuarticColumnTop1810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hd0 : ((A ^ 2 * F)).natDegree = 2 * A.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) hFne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * F)).coeff (2 * A.natDegree + F.natDegree) = A.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0]
  all_goals ring

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilonOff1810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilonOff1810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnEpsilonOff1810]

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilonOff1810_natDegree_lt_of_live_FG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0) :
    (n4QuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
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
  simp only [n4QuarticColumnEpsilonOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestOff1810_natDegree_lt_of_live_FG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hlf : (n4QuarticChamberRestLF9500810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 2 * F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL1810_natDegree_lt_of_live_FG l A B C D E F G hdpos hBz hCz hDz hEz g0 g1
  have hc1 : (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL2810_natDegree_lt_of_live_FG l A B C D E F G hdpos hBz hCz hDz hEz g2 g3
  have hc2 : (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta1810_natDegree_lt_of_live_FG beta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc3 : (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta2810_natDegree_lt_of_live_FG beta A B C D E F G hdpos hBz hCz hDz hEz g1
  have hc4 : (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
    simp only [n4QuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [n4QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnDelta810_natDegree_lt_of_live_FG delta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc6 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_FG zeta A B C D E F G hdpos hBz hCz hDz hEz g0 g1
  have hc7 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_FG eta A B C D E F G hdpos hBz hCz hDz hEz g0
  have hc8 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_FG theta A B C D E F G hdpos hBz hCz hDz hEz g0 g1
  have hc9 : (n4QuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [n4QuarticColumnEpsilonOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [n4QuarticChamberRestOff1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilonOff1810_natDegree_lt_of_live_CFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : C.natDegree + F.natDegree < d) :
    (n4QuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
  subst hBz
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnEpsilonOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestOff1810_natDegree_lt_of_live_CFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hlf : (n4QuarticChamberRestLF9500810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n4QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL1810_natDegree_lt_of_live_CFG l A B C D E F G hdpos hBz hDz hEz g0 g1 g2 g3 g4 g5
  have hc1 : (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n4QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL2810_natDegree_lt_of_live_CFG l A B C D E F G hdpos hBz hDz hEz g6 g7 g8 g9
  have hc2 : (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n4QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta1810_natDegree_lt_of_live_CFG beta A B C D E F G hdpos hBz hDz hEz g0 g1 g2 g3
  have hc3 : (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n4QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta2810_natDegree_lt_of_live_CFG beta A B C D E F G hdpos hBz hDz hEz g4
  have hc4 : (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    subst hBz
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
    omega
  have hc5 : (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnDelta810_natDegree_lt_of_live_CFG delta A B C D E F G hdpos hBz hDz hEz g0 g1 g2 g3
  have hc6 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_CFG zeta A B C D E F G hdpos hBz hDz hEz g0 g1 g2 g3
  have hc7 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_CFG eta A B C D E F G hdpos hBz hDz hEz g0
  have hc8 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_CFG theta A B C D E F G hdpos hBz hDz hEz g0 g1 g2 g3
  have hc9 : (n4QuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n4QuarticColumnEpsilonOff1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEpsilonOff1810_natDegree_lt_of_live_CFG epsilon A B C D E F G hdpos hBz hDz hEz g0
  simp only [n4QuarticChamberRestOff1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
/-- The tied top of the `gamma` column of `μ` (1 monomial, degree `G.natDegree`). -/
def muQuarticColumnTop1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 4 * gamma : k) • G

set_option maxHeartbeats 64000000 in
/-- That column without its tied top (3 monomials). -/
def muQuarticColumnGammaOff1810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGamma810_split1
    (gamma : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnGamma810 gamma A B C D E F G =
      muQuarticColumnTop1810 gamma A B C D E F G + muQuarticColumnGammaOff1810 gamma A B C D E F G := by
  simp only [muQuarticColumnGamma810, muQuarticColumnTop1810, muQuarticColumnGammaOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRestOff1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9500810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G +
    muQuarticColumnGammaOff1810 gamma A B C D E F G

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9500810_split1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    muQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticColumnTop1810 gamma A B C D E F G +
        muQuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [muQuarticChamberRest9500810, muQuarticChamberRestOff1810, muQuarticColumnGamma810, muQuarticColumnTop1810, muQuarticColumnGammaOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnTop1810_coeff
    (gamma : k)
    {A B C D E F G : k[X]}
    (hGne : G ≠ 0) :
    (muQuarticColumnTop1810 gamma A B C D E F G).coeff (G.natDegree) =
      (3 / 4 : k) * gamma * (G.leadingCoeff) := by
  simp only [muQuarticColumnTop1810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hd0 : (G).natDegree = G.natDegree := by
    all_goals omega
  have hc0 : (G).coeff (G.natDegree) = G.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0]
  all_goals ring

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGammaOff1810_zero (A B C D E F G : k[X]) :
    muQuarticColumnGammaOff1810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnGammaOff1810]

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGammaOff1810_natDegree_lt_of_live_DEG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0) :
    (muQuarticColumnGammaOff1810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hFz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnGammaOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestOff1810_natDegree_lt_of_live_DEG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hFz : F = 0)
    (hlf : (muQuarticChamberRestLF9500810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d)) :
    (muQuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_DEG l A B C D E F G hdpos hBz hCz hFz g0 g1
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | g0
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_DEG beta A B C D E F G hdpos hBz hCz hFz g0
  have hc2 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_DEG delta A B C D E F G hdpos hBz hCz hFz g0
  have hc3 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_DEG epsilon A B C D E F G hdpos hBz hCz hFz g0
  have hc4 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_DEG zeta A B C D E F G hdpos hBz hCz hFz g0
  have hc5 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
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
  have hc6 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
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
  have hc7 : (muQuarticColumnGammaOff1810 gamma A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hFz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnGammaOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRestOff1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGammaOff1810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0) :
    (muQuarticColumnGammaOff1810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnGammaOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestOff1810_natDegree_lt_of_live_DFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hEz : E = 0)
    (hlf : (muQuarticChamberRestLF9500810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d)) :
    (muQuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_DFG l A B C D E F G hdpos hBz hCz hEz g0 g1
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_DFG beta A B C D E F G hdpos hBz hCz hEz g0 g1
  have hc2 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_DFG delta A B C D E F G hdpos hBz hCz hEz g0 g1
  have hc3 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
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
  have hc4 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_DFG zeta A B C D E F G hdpos hBz hCz hEz g0
  have hc5 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
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
  have hc7 : (muQuarticColumnGammaOff1810 gamma A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnGammaOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRestOff1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- The tied top of the `epsilon` column of `N₃` (2 monomial, degree `A.natDegree + B.natDegree + C.natDegree`). -/
def n3QuarticColumnTop1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * epsilon : k) • (A * B * C)
  - (3 / 32 * epsilon : k) • (A * F)

set_option maxHeartbeats 64000000 in
/-- That column without its tied top (3 monomials). -/
def n3QuarticColumnEpsilonOff1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEpsilon810_split1
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n3QuarticColumnEpsilon810 epsilon A B C D E F G =
      n3QuarticColumnTop1810 epsilon A B C D E F G + n3QuarticColumnEpsilonOff1810 epsilon A B C D E F G := by
  simp only [n3QuarticColumnEpsilon810, n3QuarticColumnTop1810, n3QuarticColumnEpsilonOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n3QuarticChamberRestOff1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n3QuarticChamberRestLF9501810 A B C D E F G +
    n3QuarticColumnL1810 l A B C D E F G +
    n3QuarticColumnL2810 l A B C D E F G +
    n3QuarticColumnBeta810 beta A B C D E F G +
    n3QuarticColumnGamma810 gamma A B C D E F G +
    n3QuarticColumnDelta810 delta A B C D E F G +
    n3QuarticColumnZeta810 zeta A B C D E F G +
    n3QuarticColumnEta810 eta A B C D E F G +
    n3QuarticColumnTheta810 theta A B C D E F G +
    n3QuarticColumnEpsilonOff1810 epsilon A B C D E F G

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRest9501810_split1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n3QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n3QuarticColumnTop1810 epsilon A B C D E F G +
        n3QuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n3QuarticChamberRest9501810, n3QuarticChamberRestOff1810, n3QuarticColumnEpsilon810, n3QuarticColumnTop1810, n3QuarticColumnEpsilonOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnTop1810_coeff
    (epsilon : k)
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + F.natDegree = A.natDegree + B.natDegree + C.natDegree) :
    (n3QuarticColumnTop1810 epsilon A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree) =
      (3 / 64 : k) * epsilon * (A.leadingCoeff * B.leadingCoeff * C.leadingCoeff) + (-(3 / 32 : k)) * epsilon * (A.leadingCoeff * F.leadingCoeff) := by
  simp only [n3QuarticColumnTop1810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hd0 : ((A * B * C)).natDegree = A.natDegree + B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * C)).coeff (A.natDegree + B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * F)).natDegree = A.natDegree + B.natDegree + C.natDegree := by
    rw [natDegree_mul hAne hFne]
    all_goals omega
  have hc1 : ((A * F)).coeff (A.natDegree + B.natDegree + C.natDegree) = A.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEpsilonOff1810_zero (A B C D E F G : k[X]) :
    n3QuarticColumnEpsilonOff1810 0 A B C D E F G = 0 := by
  simp [n3QuarticColumnEpsilonOff1810]

set_option maxHeartbeats 64000000 in
theorem n3QuarticColumnEpsilonOff1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 3 * B.natDegree < d) :
    (n3QuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticColumnEpsilonOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestOff1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hlf : (n3QuarticChamberRestLF9501810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d)) :
    (n3QuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g11 g12
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc6 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1
  have hc7 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc8 : (n3QuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n3QuarticColumnEpsilonOff1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilonOff1810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0
  simp only [n3QuarticChamberRestOff1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- The tied top of the `epsilon` column of `N₄` (2 monomial, degree `2 * A.natDegree + B.natDegree + C.natDegree`). -/
def n4QuarticColumnTop2810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 64 * epsilon : k)) • (A ^ 2 * B * C)
  + (1 / 32 * epsilon : k) • (A ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- That column without its tied top (7 monomials). -/
def n4QuarticColumnEpsilonOff2810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 16 * epsilon : k)) • (A * B ^ 3)
  + (1 / 4 * epsilon : k) • (A * B * E)
  + (1 / 4 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilon810_split2
    (epsilon : k)
    (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilon810 epsilon A B C D E F G =
      n4QuarticColumnTop2810 epsilon A B C D E F G + n4QuarticColumnEpsilonOff2810 epsilon A B C D E F G := by
  simp only [n4QuarticColumnEpsilon810, n4QuarticColumnTop2810, n4QuarticColumnEpsilonOff2810]
  all_goals module

set_option maxHeartbeats 64000000 in
def n4QuarticChamberRestOff2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n4QuarticChamberRestLF9502810 A B C D E F G +
    n4QuarticColumnL1810 l A B C D E F G +
    n4QuarticColumnL2810 l A B C D E F G +
    n4QuarticColumnBeta1810 beta A B C D E F G +
    n4QuarticColumnBeta2810 beta A B C D E F G +
    n4QuarticColumnGamma810 gamma A B C D E F G +
    n4QuarticColumnDelta810 delta A B C D E F G +
    n4QuarticColumnZeta810 zeta A B C D E F G +
    n4QuarticColumnEta810 eta A B C D E F G +
    n4QuarticColumnTheta810 theta A B C D E F G +
    n4QuarticColumnEpsilonOff2810 epsilon A B C D E F G

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRest9502810_split2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n4QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n4QuarticColumnTop2810 epsilon A B C D E F G +
        n4QuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n4QuarticChamberRest9502810, n4QuarticChamberRestOff2810, n4QuarticColumnEpsilon810, n4QuarticColumnTop2810, n4QuarticColumnEpsilonOff2810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnTop2810_coeff
    (epsilon : k)
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : 2 * A.natDegree + F.natDegree = 2 * A.natDegree + B.natDegree + C.natDegree) :
    (n4QuarticColumnTop2810 epsilon A B C D E F G).coeff (2 * A.natDegree + B.natDegree + C.natDegree) =
      (-(1 / 64 : k)) * epsilon * (A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff) + (1 / 32 : k) * epsilon * (A.leadingCoeff ^ 2 * F.leadingCoeff) := by
  simp only [n4QuarticColumnTop2810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hd0 : ((A ^ 2 * B * C)).natDegree = 2 * A.natDegree + B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B * C)).coeff (2 * A.natDegree + B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * F)).natDegree = 2 * A.natDegree + B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) hFne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * F)).coeff (2 * A.natDegree + B.natDegree + C.natDegree) = A.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilonOff2810_zero (A B C D E F G : k[X]) :
    n4QuarticColumnEpsilonOff2810 0 A B C D E F G = 0 := by
  simp [n4QuarticColumnEpsilonOff2810]

set_option maxHeartbeats 64000000 in
theorem n4QuarticColumnEpsilonOff2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (n4QuarticColumnEpsilonOff2810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticColumnEpsilonOff2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestOff2810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hlf : (n4QuarticChamberRestLF9502810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩
    · rw [n4QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL1810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩
    · rw [n4QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL2810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g11 g12 g13 g14 g15 g16 g17
  have hc2 : (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n4QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta1810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc3 : (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n4QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta2810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g9
  have hc4 : (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n4QuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2 g3
  have hc5 : (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n4QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7
  have hc6 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc7 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc8 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc9 : (n4QuarticColumnEpsilonOff2810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [n4QuarticColumnEpsilonOff2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEpsilonOff2810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1 g2
  simp only [n4QuarticChamberRestOff2810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
/-- The tied top of the `epsilon` column of `ξ` (3 monomial, degree `A.natDegree + 2 * B.natDegree`). -/
def xiQuarticColumnTop1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • (A * B ^ 2)
  - (1 / 8 * epsilon : k) • C ^ 2
  + (1 / 2 * epsilon : k) • G

set_option maxHeartbeats 64000000 in
/-- That column without its tied top (1 monomials). -/
def xiQuarticColumnEpsilonOff1810
    (epsilon : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * epsilon : k)) • (B * D)

set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEpsilon810_split1
    (epsilon : k)
    (A B C D E F G : k[X]) :
    xiQuarticColumnEpsilon810 epsilon A B C D E F G =
      xiQuarticColumnTop1810 epsilon A B C D E F G + xiQuarticColumnEpsilonOff1810 epsilon A B C D E F G := by
  simp only [xiQuarticColumnEpsilon810, xiQuarticColumnTop1810, xiQuarticColumnEpsilonOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
def xiQuarticChamberRestOff1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  xiQuarticChamberRestLF9501810 A B C D E F G +
    xiQuarticColumnL810 l A B C D E F G +
    xiQuarticColumnBeta810 beta A B C D E F G +
    xiQuarticColumnGamma810 gamma A B C D E F G +
    xiQuarticColumnDelta810 delta A B C D E F G +
    xiQuarticColumnZeta810 zeta A B C D E F G +
    xiQuarticColumnEta810 eta A B C D E F G +
    xiQuarticColumnTheta810 theta A B C D E F G +
    xiQuarticColumnEpsilonOff1810 epsilon A B C D E F G

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest9501810_split1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    xiQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      xiQuarticColumnTop1810 epsilon A B C D E F G +
        xiQuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [xiQuarticChamberRest9501810, xiQuarticChamberRestOff1810, xiQuarticColumnEpsilon810, xiQuarticColumnTop1810, xiQuarticColumnEpsilonOff1810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnTop1810_coeff
    (epsilon : k)
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree = A.natDegree + 2 * B.natDegree)
    (ht2 : G.natDegree = A.natDegree + 2 * B.natDegree) :
    (xiQuarticColumnTop1810 epsilon A B C D E F G).coeff (A.natDegree + 2 * B.natDegree) =
      (1 / 32 : k) * epsilon * (A.leadingCoeff * B.leadingCoeff ^ 2) + (-(1 / 8 : k)) * epsilon * (C.leadingCoeff ^ 2) + (1 / 2 : k) * epsilon * (G.leadingCoeff) := by
  simp only [xiQuarticColumnTop1810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hd0 : ((A * B ^ 2)).natDegree = A.natDegree + 2 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2)).coeff (A.natDegree + 2 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 2).natDegree = A.natDegree + 2 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 2).coeff (A.natDegree + 2 * B.natDegree) = C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (G).natDegree = A.natDegree + 2 * B.natDegree := by
    all_goals omega
  have hc2 : (G).coeff (A.natDegree + 2 * B.natDegree) = G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEpsilonOff1810_zero (A B C D E F G : k[X]) :
    xiQuarticColumnEpsilonOff1810 0 A B C D E F G = 0 := by
  simp [xiQuarticColumnEpsilonOff1810]

set_option maxHeartbeats 64000000 in
theorem xiQuarticColumnEpsilonOff1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (epsilon : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0) :
    (xiQuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticColumnEpsilonOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestOff1810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hlf : (xiQuarticChamberRestLF9501810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d)) :
    (xiQuarticChamberRestOff1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc4 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1
  have hc5 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0
  have hc6 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (xiQuarticColumnEpsilonOff1810 epsilon A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [xiQuarticColumnEpsilonOff1810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [xiQuarticChamberRestOff1810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- The tied top of the `gamma` column of `μ` (1 monomial, degree `G.natDegree`). -/
def muQuarticColumnTop2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 4 * gamma : k) • G

set_option maxHeartbeats 64000000 in
/-- That column without its tied top (3 monomials). -/
def muQuarticColumnGammaOff2810
    (gamma : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 128 * gamma : k) • (A * B ^ 2)
  - (3 / 16 * gamma : k) • (B * D)
  - (3 / 32 * gamma : k) • C ^ 2

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGamma810_split2
    (gamma : k)
    (A B C D E F G : k[X]) :
    muQuarticColumnGamma810 gamma A B C D E F G =
      muQuarticColumnTop2810 gamma A B C D E F G + muQuarticColumnGammaOff2810 gamma A B C D E F G := by
  simp only [muQuarticColumnGamma810, muQuarticColumnTop2810, muQuarticColumnGammaOff2810]
  all_goals module

set_option maxHeartbeats 64000000 in
def muQuarticChamberRestOff2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  muQuarticChamberRestLF9502810 A B C D E F G +
    muQuarticColumnL810 l A B C D E F G +
    muQuarticColumnBeta810 beta A B C D E F G +
    muQuarticColumnDelta810 delta A B C D E F G +
    muQuarticColumnEpsilon810 epsilon A B C D E F G +
    muQuarticColumnZeta810 zeta A B C D E F G +
    muQuarticColumnEta810 eta A B C D E F G +
    muQuarticColumnTheta810 theta A B C D E F G +
    muQuarticColumnGammaOff2810 gamma A B C D E F G

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9502810_split2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    muQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      muQuarticColumnTop2810 gamma A B C D E F G +
        muQuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [muQuarticChamberRest9502810, muQuarticChamberRestOff2810, muQuarticColumnGamma810, muQuarticColumnTop2810, muQuarticColumnGammaOff2810]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnTop2810_coeff
    (gamma : k)
    {A B C D E F G : k[X]}
    (hGne : G ≠ 0) :
    (muQuarticColumnTop2810 gamma A B C D E F G).coeff (G.natDegree) =
      (3 / 4 : k) * gamma * (G.leadingCoeff) := by
  simp only [muQuarticColumnTop2810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hd0 : (G).natDegree = G.natDegree := by
    all_goals omega
  have hc0 : (G).coeff (G.natDegree) = G.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0]
  all_goals ring

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGammaOff2810_zero (A B C D E F G : k[X]) :
    muQuarticColumnGammaOff2810 0 A B C D E F G = 0 := by
  simp [muQuarticColumnGammaOff2810]

set_option maxHeartbeats 64000000 in
theorem muQuarticColumnGammaOff2810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (gamma : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0) :
    (muQuarticColumnGammaOff2810 gamma A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticColumnGammaOff2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestOff2810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hlf : (muQuarticChamberRestLF9502810 A B C D E F G).natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d)) :
    (muQuarticChamberRestOff2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1
  have hc2 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc3 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc4 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0
  have hc5 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (muQuarticColumnGammaOff2810 gamma A B C D E F G).natDegree < d := by
    subst hBz
    subst hCz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [muQuarticColumnGammaOff2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRestOff2810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hlf hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7


end QuarticChamberUnownedTreePieces810

end Max11DegreeRoutes
