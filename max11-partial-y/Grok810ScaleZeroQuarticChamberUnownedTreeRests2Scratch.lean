import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns10Scratch
import Grok810ScaleZeroQuarticChamberUnownedRefineColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreeColumns2Scratch

/-! # UnownedTree chamber rests, part 2/4

40 of the 54 load-free and 54 full (packet,
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

section QuarticChamberUnownedTreeRests2810

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticChamberRestLF9500810` on the live set `BCFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9500810PartBCFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 128 : k) • (A * B * C * G)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9500810PartBCFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 5 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF9500810PartBCFG1810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9500810PartBCFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticChamberRestLF9500810` on the live set `BCFG` (4 monomials). -/
def primitiveQuarticChamberRestLF9500810PartBCFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * F ^ 2)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9500810PartBCFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + G.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + 2 * F.natDegree < d) :
    (primitiveQuarticChamberRestLF9500810PartBCFG2810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9500810PartBCFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9500810_split_of_live_BCFG
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0) :
    primitiveQuarticChamberRestLF9500810 A B C D E F G =
      primitiveQuarticChamberRestLF9500810PartBCFG1810 A B C D E F G +
        primitiveQuarticChamberRestLF9500810PartBCFG2810 A B C D E F G := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticChamberRestLF9500810, primitiveQuarticChamberRestLF9500810PartBCFG1810, primitiveQuarticChamberRestLF9500810PartBCFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9500810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 5 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd6 : 3 * B.natDegree + G.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd9 : B.natDegree + 2 * F.natDegree < d) :
    (primitiveQuarticChamberRestLF9500810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF9500810_split_of_live_BCFG A B C D E F G hDz hEz]
  exact (natDegree_add_lt810 (primitiveQuarticChamberRestLF9500810PartBCFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF9500810PartBCFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9))

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest9500810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl1 : A.natDegree + 5 * B.natDegree < d)
    (hl2 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl6 : 3 * B.natDegree + G.natDegree < d)
    (hl7 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl8 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl9 : B.natDegree + 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF9500810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9
  have hc0 : (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [primitiveQuarticColumnL1810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL1810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc1 : (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [primitiveQuarticColumnL2810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL2810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g12 g13 g14 g15 g16 g17 g18
  have hc2 : (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [primitiveQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc3 : (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc4 : (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [primitiveQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc6 : (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [primitiveQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc7 : (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [primitiveQuarticColumnEta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1 g2 g3
  have hc8 : (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [primitiveQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  simp only [primitiveQuarticChamberRest9500810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0) :
    (xiQuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF9501810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hbl : l = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d)) :
    (xiQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz
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
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
  simp only [xiQuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0) :
    (n2QuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticChamberRestLF9501810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRest9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * B.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (n2QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n2QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz
  have hc0 : (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n2QuarticColumnL810_zero]
      simpa using hdpos
    · exact n2QuarticColumnL810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n2QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc2 : (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [n2QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n2QuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0
  have hc3 : (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n2QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc4 : (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1
  have hc5 : (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [n2QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc6 : (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    subst hDz
    subst hEz
    have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
    have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
    have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
    have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
    have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
    have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
    have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
    simp only [n2QuarticColumnEta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc7 : (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1
  simp only [n2QuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 5 * B.natDegree < d) :
    (n3QuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticChamberRestLF9501810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRest9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : 5 * B.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d)) :
    (n3QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0
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
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2
  simp only [n3QuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9502810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 5 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 3 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + 2 * F.natDegree < d) :
    (n4QuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRest9502810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : A.natDegree + 5 * B.natDegree < d)
    (hl1 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 3 * B.natDegree + G.natDegree < d)
    (hl3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl4 : B.natDegree + 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n4QuarticChamberRestLF9502810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0 hl1 hl2 hl3 hl4
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
  have hc6 : (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n4QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc7 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc8 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc9 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  simp only [n4QuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
theorem n5QuarticChamberRestLF9500810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : 5 * B.natDegree < d) :
    (n5QuarticChamberRestLF9500810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n5QuarticChamberRestLF9500810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticChamberRest9500810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : 5 * B.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d)) :
    (n5QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n5QuarticChamberRestLF9500810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0
  have hc0 : (n5QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
    · rw [n5QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n5QuarticColumnL1810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (n5QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
    · rw [n5QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n5QuarticColumnL2810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g11 g12 g13
  have hc2 : (n5QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n5QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n5QuarticColumnBeta810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc3 : (n5QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [n5QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n5QuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc4 : (n5QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n5QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n5QuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (n5QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n5QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n5QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0
  have hc6 : (n5QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n5QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n5QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc7 : (n5QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n5QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n5QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1
  have hc8 : (n5QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [n5QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n5QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2
  simp only [n5QuarticChamberRest9500810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 5 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 3 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + 2 * F.natDegree < d) :
    (n6QuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n6QuarticChamberRestLF9501810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n6QuarticChamberRest9501810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : A.natDegree + 5 * B.natDegree < d)
    (hl1 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 3 * B.natDegree + G.natDegree < d)
    (hl3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl4 : B.natDegree + 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n6QuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n6QuarticChamberRestLF9501810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0 hl1 hl2 hl3 hl4
  have hc0 : (n6QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩
    · rw [n6QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n6QuarticColumnL1810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (n6QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩
    · rw [n6QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n6QuarticColumnL2810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g11 g12 g13 g14 g15 g16 g17
  have hc2 : (n6QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [n6QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n6QuarticColumnBeta1810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc3 : (n6QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [n6QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n6QuarticColumnBeta2810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g10
  have hc4 : (n6QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n6QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n6QuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  have hc5 : (n6QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n6QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc6 : (n6QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [n6QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n6QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc7 : (n6QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n6QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc8 : (n6QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [n6QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1 g2
  have hc9 : (n6QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n6QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n6QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  simp only [n6QuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
theorem n7QuarticChamberRestLF9500810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hd0 : A.natDegree + 5 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd2 : 3 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + 2 * F.natDegree < d) :
    (n7QuarticChamberRestLF9500810 A B C D E F G).natDegree < d := by
  subst hDz
  subst hEz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n7QuarticChamberRestLF9500810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n7QuarticChamberRest9500810_natDegree_lt_of_live_BCFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hl0 : A.natDegree + 5 * B.natDegree < d)
    (hl1 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl2 : 3 * B.natDegree + G.natDegree < d)
    (hl3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl4 : B.natDegree + 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n7QuarticChamberRest9500810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n7QuarticChamberRestLF9500810_natDegree_lt_of_live_BCFG
      A B C D E F G hdpos hDz hEz hl0 hl1 hl2 hl3 hl4
  have hc0 : (n7QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [n7QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n7QuarticColumnL1810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc1 : (n7QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18⟩
    · rw [n7QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n7QuarticColumnL2810_natDegree_lt_of_live_BCFG l A B C D E F G hdpos hDz hEz g12 g13 g14 g15 g16 g17 g18
  have hc2 : (n7QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [n7QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n7QuarticColumnBeta1810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc3 : (n7QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [n7QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n7QuarticColumnBeta2810_natDegree_lt_of_live_BCFG beta A B C D E F G hdpos hDz hEz g11
  have hc4 : (n7QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n7QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n7QuarticColumnGamma810_natDegree_lt_of_live_BCFG gamma A B C D E F G hdpos hDz hEz g0 g1 g2 g3
  have hc5 : (n7QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n7QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n7QuarticColumnDelta810_natDegree_lt_of_live_BCFG delta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc6 : (n7QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [n7QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n7QuarticColumnEpsilon810_natDegree_lt_of_live_BCFG epsilon A B C D E F G hdpos hDz hEz g0 g1
  have hc7 : (n7QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n7QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n7QuarticColumnZeta810_natDegree_lt_of_live_BCFG zeta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4 g5 g6
  have hc8 : (n7QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n7QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n7QuarticColumnEta810_natDegree_lt_of_live_BCFG eta A B C D E F G hdpos hDz hEz g0 g1
  have hc9 : (n7QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n7QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n7QuarticColumnTheta810_natDegree_lt_of_live_BCFG theta A B C D E F G hdpos hDz hEz g0 g1 g2 g3 g4
  simp only [n7QuarticChamberRest9500810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9501810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0) :
    (kappaQuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9501810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest9501810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF9501810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2 g3
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0
  simp only [kappaQuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : A.natDegree + D.natDegree + F.natDegree < d)
    (hl1 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0 hl1
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0 g1
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_DEFG eta A B C D E F G hdpos hBz hCz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0
  simp only [xiQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 3 * D.natDegree < d)
    (hd1 : F.natDegree + G.natDegree < d) :
    (n3QuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRest9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : 3 * D.natDegree < d)
    (hl1 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ E.natDegree < d)) :
    (n3QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0 hl1
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4 g5
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g6 g7
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_DEFG eta A B C D E F G hdpos hBz hCz g0 g1
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0 g1
  simp only [n3QuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9503810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : A.natDegree + 3 * D.natDegree < d)
    (hd1 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd2 : 2 * D.natDegree + F.natDegree < d)
    (hd3 : D.natDegree + 2 * E.natDegree < d) :
    (n4QuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticChamberRestLF9503810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRest9503810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : A.natDegree + 3 * D.natDegree < d)
    (hl1 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl2 : 2 * D.natDegree + F.natDegree < d)
    (hl3 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + D.natDegree + E.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n4QuarticChamberRestLF9503810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0 hl1 hl2 hl3
  have hc0 : (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n4QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL1810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4 g5
  have hc1 : (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n4QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL2810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g6 g7 g8
  have hc2 : (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n4QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta1810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4
  have hc3 : (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n4QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta2810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g5
  have hc4 : (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n4QuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0 g1
  have hc5 : (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n4QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4
  have hc6 : (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0 g1
  have hc7 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0 g1 g2 g3
  have hc8 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_DEFG eta A B C D E F G hdpos hBz hCz g0 g1
  have hc9 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0 g1
  simp only [n4QuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * D.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (G.natDegree < d))
    (hbtheta : theta = 0 ∨ (F.natDegree < d)) :
    (piQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g3 g4
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_DEFG eta A B C D E F G hdpos hBz hCz g0
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0
  simp only [piQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9503810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF9503810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest9503810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF9503810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0 g1
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_DEFG eta A B C D E F G hdpos hBz hCz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0
  simp only [xiQuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9504810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : E.natDegree + G.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF9504810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF9504810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest9504810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : E.natDegree + G.natDegree < d)
    (hl1 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest9504810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF9504810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0 hl1
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_DEFG l A B C D E F G hdpos hBz hCz g0 g1 g2 g3 g4
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_DEFG beta A B C D E F G hdpos hBz hCz g0 g1 g2
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0 g1
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_DEFG eta A B C D E F G hdpos hBz hCz g0
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_DEFG theta A B C D E F G hdpos hBz hCz g0
  simp only [xiQuarticChamberRest9504810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  subst hBz
  subst hCz
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9502810_natDegree_lt_of_live_DEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hCz : C = 0)
    (hl0 : A.natDegree + 2 * D.natDegree < d)
    (hl1 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (G.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + D.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (D.natDegree < d)) :
    (muQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9502810_natDegree_lt_of_live_DEFG
      A B C D E F G hdpos hBz hCz hl0 hl1
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
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_DEFG gamma A B C D E F G hdpos hBz hCz g0
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_DEFG delta A B C D E F G hdpos hBz hCz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_DEFG epsilon A B C D E F G hdpos hBz hCz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_DEFG zeta A B C D E F G hdpos hBz hCz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
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
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + D.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [kappaQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [kappaQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `muQuarticChamberRestLF9503810` on the live set `BCDEFG` (6 monomials). -/
def muQuarticChamberRestLF9503810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * C)
  + (35 / 2048 : k) • B ^ 4
  - (5 / 64 : k) • (A * B * F)
  - (5 / 128 : k) • (A * D ^ 2)
  - (15 / 128 : k) • (B ^ 2 * E)
  - (15 / 64 : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9503810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd1 : 4 * B.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * B.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + D.natDegree < d) :
    (muQuarticChamberRestLF9503810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [muQuarticChamberRestLF9503810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `muQuarticChamberRestLF9503810` on the live set `BCDEFG` (1 monomials). -/
def muQuarticChamberRestLF9503810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (D * F)

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9503810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : D.natDegree + F.natDegree < d) :
    (muQuarticChamberRestLF9503810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [muQuarticChamberRestLF9503810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9503810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF9503810 A B C D E F G =
      muQuarticChamberRestLF9503810PartBCDEFG1810 A B C D E F G +
        muQuarticChamberRestLF9503810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [muQuarticChamberRestLF9503810, muQuarticChamberRestLF9503810PartBCDEFG1810, muQuarticChamberRestLF9503810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
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
    (muQuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  rw [muQuarticChamberRestLF9503810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (muQuarticChamberRestLF9503810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (muQuarticChamberRestLF9503810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hl1 : 4 * B.natDegree < d)
    (hl2 : A.natDegree + B.natDegree + F.natDegree < d)
    (hl3 : A.natDegree + 2 * D.natDegree < d)
    (hl4 : 2 * B.natDegree + E.natDegree < d)
    (hl5 : B.natDegree + C.natDegree + D.natDegree < d)
    (hl6 : D.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [muQuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * D.natDegree < d) :
    (n2QuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticChamberRestLF9502810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRest9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : 3 * B.natDegree + C.natDegree < d)
    (hl2 : 2 * B.natDegree + F.natDegree < d)
    (hl3 : B.natDegree + 2 * D.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (n2QuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n2QuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3
  have hc0 : (n2QuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩
    · rw [n2QuarticColumnL810_zero]
      simpa using hdpos
    · exact n2QuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17
  have hc1 : (n2QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [n2QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc2 : (n2QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [n2QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n2QuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2
  have hc3 : (n2QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n2QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc4 : (n2QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1
  have hc5 : (n2QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n2QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3
  have hc6 : (n2QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [n2QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0
  have hc7 : (n2QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [n2QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n2QuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1
  simp only [n2QuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n3QuarticChamberRestLF9503810` on the live set `BCDEFG` (6 monomials). -/
def n3QuarticChamberRestLF9503810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (175 / 8192 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (85 / 2048 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9503810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : 5 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + E.natDegree < d) :
    (n3QuarticChamberRestLF9503810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [n3QuarticChamberRestLF9503810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n3QuarticChamberRestLF9503810` on the live set `BCDEFG` (6 monomials). -/
def n3QuarticChamberRestLF9503810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9503810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : B.natDegree + 3 * C.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + 2 * E.natDegree < d)
    (hd5 : 2 * C.natDegree + F.natDegree < d) :
    (n3QuarticChamberRestLF9503810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [n3QuarticChamberRestLF9503810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n3QuarticChamberRestLF9503810` on the live set `BCDEFG` (3 monomials). -/
def n3QuarticChamberRestLF9503810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 128 : k)) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9503810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 3 * D.natDegree < d)
    (hd2 : F.natDegree + G.natDegree < d) :
    (n3QuarticChamberRestLF9503810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [n3QuarticChamberRestLF9503810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9503810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    n3QuarticChamberRestLF9503810 A B C D E F G =
      n3QuarticChamberRestLF9503810PartBCDEFG1810 A B C D E F G +
        n3QuarticChamberRestLF9503810PartBCDEFG2810 A B C D E F G +
        n3QuarticChamberRestLF9503810PartBCDEFG3810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticChamberRestLF9503810, n3QuarticChamberRestLF9503810PartBCDEFG1810, n3QuarticChamberRestLF9503810PartBCDEFG2810, n3QuarticChamberRestLF9503810PartBCDEFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : 5 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + E.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd7 : B.natDegree + 3 * C.natDegree < d)
    (hd8 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd9 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd10 : B.natDegree + 2 * E.natDegree < d)
    (hd11 : 2 * C.natDegree + F.natDegree < d)
    (hd12 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd13 : 3 * D.natDegree < d)
    (hd14 : F.natDegree + G.natDegree < d) :
    (n3QuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  rw [n3QuarticChamberRestLF9503810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n3QuarticChamberRestLF9503810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticChamberRestLF9503810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n3QuarticChamberRestLF9503810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14))

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRest9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl2 : 5 * B.natDegree < d)
    (hl3 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl4 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl5 : 3 * B.natDegree + E.natDegree < d)
    (hl6 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl7 : B.natDegree + 3 * C.natDegree < d)
    (hl8 : B.natDegree + C.natDegree + G.natDegree < d)
    (hl9 : B.natDegree + D.natDegree + F.natDegree < d)
    (hl10 : B.natDegree + 2 * E.natDegree < d)
    (hl11 : 2 * C.natDegree + F.natDegree < d)
    (hl12 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl13 : 3 * D.natDegree < d)
    (hl14 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d)) :
    (n3QuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14
  have hc0 : (n3QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [n3QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (n3QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [n3QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n3QuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25
  have hc2 : (n3QuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩
    · rw [n3QuarticColumnBeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have hc3 : (n3QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n3QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n3QuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc4 : (n3QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [n3QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc5 : (n3QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [n3QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc6 : (n3QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [n3QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc7 : (n3QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [n3QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2
  have hc8 : (n3QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [n3QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n3QuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1 g2 g3
  simp only [n3QuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8


end QuarticChamberUnownedTreeRests2810

end Max11DegreeRoutes
