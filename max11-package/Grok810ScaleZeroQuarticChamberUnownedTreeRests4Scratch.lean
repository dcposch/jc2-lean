import Grok810ScaleZeroQuarticChamberUnownedSystemColumns9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns10Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePackets2Scratch

/-! # UnownedTree chamber rests, part 4/4

4 of the 54 load-free and 54 full (packet,
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

section QuarticChamberUnownedTreeRests4810

set_option maxHeartbeats 64000000 in
/-- Piece 1/4 of `omicronQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF9502810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 2 * B * C ^ 2)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * B * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9502810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd4 : 5 * B.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF9502810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9502810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/4 of `omicronQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF9502810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9502810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd4 : 3 * B.natDegree + E.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + D.natDegree < d) :
    (omicronQuarticChamberRestLF9502810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9502810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/4 of `omicronQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF9502810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9502810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 3 * C.natDegree < d)
    (hd1 : A.natDegree + D.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + 2 * E.natDegree < d) :
    (omicronQuarticChamberRestLF9502810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9502810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/4 of `omicronQuarticChamberRestLF9502810` on the live set `BCDEFG` (4 monomials). -/
def omicronQuarticChamberRestLF9502810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9502810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * C.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 3 * D.natDegree < d)
    (hd3 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF9502810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9502810PartBCDEFG4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9502810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF9502810 A B C D E F G =
      omicronQuarticChamberRestLF9502810PartBCDEFG1810 A B C D E F G +
        omicronQuarticChamberRestLF9502810PartBCDEFG2810 A B C D E F G +
        omicronQuarticChamberRestLF9502810PartBCDEFG3810 A B C D E F G +
        omicronQuarticChamberRestLF9502810PartBCDEFG4810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticChamberRestLF9502810, omicronQuarticChamberRestLF9502810PartBCDEFG1810, omicronQuarticChamberRestLF9502810PartBCDEFG2810, omicronQuarticChamberRestLF9502810PartBCDEFG3810, omicronQuarticChamberRestLF9502810PartBCDEFG4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd4 : 5 * B.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + G.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd9 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : 3 * B.natDegree + E.natDegree < d)
    (hd11 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : B.natDegree + 3 * C.natDegree < d)
    (hd13 : A.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd16 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd17 : B.natDegree + 2 * E.natDegree < d)
    (hd18 : 2 * C.natDegree + F.natDegree < d)
    (hd19 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd20 : 3 * D.natDegree < d)
    (hd21 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  rw [omicronQuarticChamberRestLF9502810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticChamberRestLF9502810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticChamberRestLF9502810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticChamberRestLF9502810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (omicronQuarticChamberRestLF9502810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21))

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRest9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hl3 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl4 : 5 * B.natDegree < d)
    (hl5 : 2 * A.natDegree + B.natDegree + G.natDegree < d)
    (hl6 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl7 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl8 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl9 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl10 : 3 * B.natDegree + E.natDegree < d)
    (hl11 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl12 : B.natDegree + 3 * C.natDegree < d)
    (hl13 : A.natDegree + D.natDegree + G.natDegree < d)
    (hl14 : A.natDegree + E.natDegree + F.natDegree < d)
    (hl15 : B.natDegree + C.natDegree + G.natDegree < d)
    (hl16 : B.natDegree + D.natDegree + F.natDegree < d)
    (hl17 : B.natDegree + 2 * E.natDegree < d)
    (hl18 : 2 * C.natDegree + F.natDegree < d)
    (hl19 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl20 : 3 * D.natDegree < d)
    (hl21 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d)) :
    (omicronQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21
  have hc0 : (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24⟩
    · rw [omicronQuarticColumnL1810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24⟩
    · rw [omicronQuarticColumnL2810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24
  have hc2 : (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [omicronQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc3 : (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [omicronQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc4 : (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [omicronQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc5 : (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [omicronQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc6 : (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [omicronQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc7 : (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [omicronQuarticColumnEta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3
  have hc8 : (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [omicronQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1 g2 g3
  simp only [omicronQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/6 of `primitiveQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9502810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 5 * B.natDegree < d)
    (hd5 : 3 * A.natDegree + B.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9502810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/6 of `primitiveQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9502810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd2 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9502810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/6 of `primitiveQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9502810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 1024 : k)) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd1 : 4 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * A.natDegree + D.natDegree + G.natDegree < d)
    (hd4 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9502810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/6 of `primitiveQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9502810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 3 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + G.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + F.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9502810PartBCDEFG4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 5/6 of `primitiveQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9502810PartBCDEFG5810
    (A B C D E F G : k[X]) : k[X] :=
  (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810PartBCDEFG5810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + E.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810PartBCDEFG5810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9502810PartBCDEFG5810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 6/6 of `primitiveQuarticChamberRestLF9502810` on the live set `BCDEFG` (5 monomials). -/
def primitiveQuarticChamberRestLF9502810PartBCDEFG6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810PartBCDEFG6810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd3 : 2 * D.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810PartBCDEFG6810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9502810PartBCDEFG6810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF9502810 A B C D E F G =
      primitiveQuarticChamberRestLF9502810PartBCDEFG1810 A B C D E F G +
        primitiveQuarticChamberRestLF9502810PartBCDEFG2810 A B C D E F G +
        primitiveQuarticChamberRestLF9502810PartBCDEFG3810 A B C D E F G +
        primitiveQuarticChamberRestLF9502810PartBCDEFG4810 A B C D E F G +
        primitiveQuarticChamberRestLF9502810PartBCDEFG5810 A B C D E F G +
        primitiveQuarticChamberRestLF9502810PartBCDEFG6810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticChamberRestLF9502810, primitiveQuarticChamberRestLF9502810PartBCDEFG1810, primitiveQuarticChamberRestLF9502810PartBCDEFG2810, primitiveQuarticChamberRestLF9502810PartBCDEFG3810, primitiveQuarticChamberRestLF9502810PartBCDEFG4810, primitiveQuarticChamberRestLF9502810PartBCDEFG5810, primitiveQuarticChamberRestLF9502810PartBCDEFG6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 5 * B.natDegree < d)
    (hd5 : 3 * A.natDegree + B.natDegree + G.natDegree < d)
    (hd6 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd7 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd8 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd9 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd13 : 4 * B.natDegree + D.natDegree < d)
    (hd14 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd15 : 2 * A.natDegree + D.natDegree + G.natDegree < d)
    (hd16 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd17 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd18 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd19 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd20 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd21 : A.natDegree + 3 * D.natDegree < d)
    (hd22 : 3 * B.natDegree + G.natDegree < d)
    (hd23 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd24 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd25 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd26 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd27 : 3 * C.natDegree + D.natDegree < d)
    (hd28 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd29 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd30 : B.natDegree + 2 * F.natDegree < d)
    (hd31 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd32 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd33 : 2 * D.natDegree + F.natDegree < d)
    (hd34 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF9502810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticChamberRestLF9502810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF9502810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticChamberRestLF9502810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (primitiveQuarticChamberRestLF9502810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21 hd22 hd23)) (primitiveQuarticChamberRestLF9502810PartBCDEFG5810_natDegree_lt A B C D E F G hdpos hd24 hd25 hd26 hd27 hd28 hd29)) (primitiveQuarticChamberRestLF9502810PartBCDEFG6810_natDegree_lt A B C D E F G hdpos hd30 hd31 hd32 hd33 hd34))

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hl3 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl4 : A.natDegree + 5 * B.natDegree < d)
    (hl5 : 3 * A.natDegree + B.natDegree + G.natDegree < d)
    (hl6 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl7 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl8 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl9 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl10 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hl11 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl12 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl13 : 4 * B.natDegree + D.natDegree < d)
    (hl14 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl15 : 2 * A.natDegree + D.natDegree + G.natDegree < d)
    (hl16 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hl17 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl18 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hl19 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hl20 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl21 : A.natDegree + 3 * D.natDegree < d)
    (hl22 : 3 * B.natDegree + G.natDegree < d)
    (hl23 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl24 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hl25 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hl26 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl27 : 3 * C.natDegree + D.natDegree < d)
    (hl28 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl29 : B.natDegree + E.natDegree + G.natDegree < d)
    (hl30 : B.natDegree + 2 * F.natDegree < d)
    (hl31 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl32 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl33 : 2 * D.natDegree + F.natDegree < d)
    (hl34 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + B.natDegree + D.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 2 * B.natDegree + C.natDegree + E.natDegree < d ∧ 2 * B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + E.natDegree + G.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ B.natDegree + D.natDegree + G.natDegree < d ∧ B.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25 hl26 hl27 hl28 hl29 hl30 hl31 hl32 hl33 hl34
  have hc0 : (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39⟩
    · rw [primitiveQuarticColumnL1810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39⟩
    · rw [primitiveQuarticColumnL2810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37 g38 g39
  have hc2 : (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19⟩
    · rw [primitiveQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc3 : (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [primitiveQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc4 : (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [primitiveQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc5 : (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [primitiveQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc6 : (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [primitiveQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc7 : (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnEta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  have hc8 : (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6
  simp only [primitiveQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8


end QuarticChamberUnownedTreeRests4810

end Max11DegreeRoutes
