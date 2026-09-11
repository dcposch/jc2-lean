import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns10Scratch
import Grok810ScaleZeroQuarticChamberUnownedColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedTreePackets2Scratch

/-! # UnownedTree chamber rests, part 3/4

22 of the 54 load-free and 54 full (packet,
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

section QuarticChamberUnownedTreeRests3810

set_option maxHeartbeats 64000000 in
/-- Piece 1/5 of `n4QuarticChamberRestLF9504810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9504810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 3 * B ^ 2 * D)
  + (155 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (107 / 8192 : k) • (A * B ^ 5)
  - (55 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (95 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (45 / 512 : k) • (A * B ^ 3 * E)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 5 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd5 : A.natDegree + 3 * B.natDegree + E.natDegree < d) :
    (n4QuarticChamberRestLF9504810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9504810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/5 of `n4QuarticChamberRestLF9504810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9504810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(135 / 512 : k)) • (A * B ^ 2 * C * D)
  - (15 / 256 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * G)
  + (5 / 16 : k) • (A * B * D * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd2 : 4 * B.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d) :
    (n4QuarticChamberRestLF9504810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9504810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/5 of `n4QuarticChamberRestLF9504810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9504810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 32 : k) • (A * B * E ^ 2)
  + (5 / 64 : k) • (A * C ^ 2 * F)
  + (5 / 16 : k) • (A * C * D * E)
  + (5 / 64 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 3 * D.natDegree < d)
    (hd4 : 3 * B.natDegree + G.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + F.natDegree < d) :
    (n4QuarticChamberRestLF9504810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9504810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/5 of `n4QuarticChamberRestLF9504810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9504810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 8 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd3 : 3 * C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + E.natDegree + G.natDegree < d) :
    (n4QuarticChamberRestLF9504810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9504810PartBCDEFG4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 5/5 of `n4QuarticChamberRestLF9504810` on the live set `BCDEFG` (5 monomials). -/
def n4QuarticChamberRestLF9504810PartBCDEFG5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810PartBCDEFG5810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd2 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd3 : 2 * D.natDegree + F.natDegree < d)
    (hd4 : D.natDegree + 2 * E.natDegree < d) :
    (n4QuarticChamberRestLF9504810PartBCDEFG5810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9504810PartBCDEFG5810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    n4QuarticChamberRestLF9504810 A B C D E F G =
      n4QuarticChamberRestLF9504810PartBCDEFG1810 A B C D E F G +
        n4QuarticChamberRestLF9504810PartBCDEFG2810 A B C D E F G +
        n4QuarticChamberRestLF9504810PartBCDEFG3810 A B C D E F G +
        n4QuarticChamberRestLF9504810PartBCDEFG4810 A B C D E F G +
        n4QuarticChamberRestLF9504810PartBCDEFG5810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticChamberRestLF9504810, n4QuarticChamberRestLF9504810PartBCDEFG1810, n4QuarticChamberRestLF9504810PartBCDEFG2810, n4QuarticChamberRestLF9504810PartBCDEFG3810, n4QuarticChamberRestLF9504810PartBCDEFG4810, n4QuarticChamberRestLF9504810PartBCDEFG5810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9504810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 5 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd5 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd8 : 4 * B.natDegree + D.natDegree < d)
    (hd9 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd10 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd13 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd14 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd15 : A.natDegree + 3 * D.natDegree < d)
    (hd16 : 3 * B.natDegree + G.natDegree < d)
    (hd17 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd18 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd19 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd20 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd21 : 3 * C.natDegree + D.natDegree < d)
    (hd22 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd23 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd24 : B.natDegree + 2 * F.natDegree < d)
    (hd25 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd26 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd27 : 2 * D.natDegree + F.natDegree < d)
    (hd28 : D.natDegree + 2 * E.natDegree < d) :
    (n4QuarticChamberRestLF9504810 A B C D E F G).natDegree < d := by
  rw [n4QuarticChamberRestLF9504810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticChamberRestLF9504810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticChamberRestLF9504810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticChamberRestLF9504810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (n4QuarticChamberRestLF9504810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21 hd22 hd23)) (n4QuarticChamberRestLF9504810PartBCDEFG5810_natDegree_lt A B C D E F G hdpos hd24 hd25 hd26 hd27 hd28))

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRest9504810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + 5 * B.natDegree < d)
    (hl3 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl4 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl5 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hl6 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl7 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl8 : 4 * B.natDegree + D.natDegree < d)
    (hl9 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl10 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl11 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hl12 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hl13 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hl14 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl15 : A.natDegree + 3 * D.natDegree < d)
    (hl16 : 3 * B.natDegree + G.natDegree < d)
    (hl17 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl18 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hl19 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hl20 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl21 : 3 * C.natDegree + D.natDegree < d)
    (hl22 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl23 : B.natDegree + E.natDegree + G.natDegree < d)
    (hl24 : B.natDegree + 2 * F.natDegree < d)
    (hl25 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl26 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl27 : 2 * D.natDegree + F.natDegree < d)
    (hl28 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + B.natDegree + D.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 2 * B.natDegree + C.natDegree + E.natDegree < d ∧ 2 * B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ B.natDegree + D.natDegree + G.natDegree < d ∧ B.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRest9504810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n4QuarticChamberRestLF9504810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25 hl26 hl27 hl28
  have hc0 : (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37⟩
    · rw [n4QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37⟩
    · rw [n4QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37
  have hc2 : (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21⟩
    · rw [n4QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta1810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc3 : (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21⟩
    · rw [n4QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta2810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g20 g21
  have hc4 : (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [n4QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n4QuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc5 : (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩
    · rw [n4QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have hc6 : (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n4QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc7 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc8 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc9 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  simp only [n4QuarticChamberRest9504810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def nuQuarticChamberRestLF9501810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9501810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d) :
    (nuQuarticChamberRestLF9501810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [nuQuarticChamberRestLF9501810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticChamberRestLF9501810` on the live set `BCDEFG` (3 monomials). -/
def nuQuarticChamberRestLF9501810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9501810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * C.natDegree + D.natDegree < d)
    (hd1 : D.natDegree + G.natDegree < d)
    (hd2 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF9501810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [nuQuarticChamberRestLF9501810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9501810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF9501810 A B C D E F G =
      nuQuarticChamberRestLF9501810PartBCDEFG1810 A B C D E F G +
        nuQuarticChamberRestLF9501810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticChamberRestLF9501810, nuQuarticChamberRestLF9501810PartBCDEFG1810, nuQuarticChamberRestLF9501810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9501810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d)
    (hd6 : 2 * C.natDegree + D.natDegree < d)
    (hd7 : D.natDegree + G.natDegree < d)
    (hd8 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  rw [nuQuarticChamberRestLF9501810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (nuQuarticChamberRestLF9501810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticChamberRestLF9501810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRest9501810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 3 * B.natDegree + C.natDegree < d)
    (hl3 : 2 * B.natDegree + F.natDegree < d)
    (hl4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hl5 : B.natDegree + 2 * D.natDegree < d)
    (hl6 : 2 * C.natDegree + D.natDegree < d)
    (hl7 : D.natDegree + G.natDegree < d)
    (hl8 : E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF9501810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8
  have hc0 : (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩
    · rw [nuQuarticColumnL810_zero]
      simpa using hdpos
    · exact nuQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have hc1 : (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [nuQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc2 : (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [nuQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact nuQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc3 : (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [nuQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc4 : (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2
  have hc5 : (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2
  have hc6 : (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnEta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1
  have hc7 : (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1
  simp only [nuQuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/4 of `omicronQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF9501810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9501810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : 5 * B.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d) :
    (omicronQuarticChamberRestLF9501810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9501810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/4 of `omicronQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF9501810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 1024 : k) • (A * B * D ^ 2)
  + (15 / 1024 : k) • (A * C ^ 2 * D)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * D * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9501810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd1 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : B.natDegree + 3 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF9501810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9501810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/4 of `omicronQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF9501810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9501810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 2 * E.natDegree < d)
    (hd4 : 2 * C.natDegree + F.natDegree < d)
    (hd5 : C.natDegree + D.natDegree + E.natDegree < d) :
    (omicronQuarticChamberRestLF9501810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9501810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/4 of `omicronQuarticChamberRestLF9501810` on the live set `BCDEFG` (2 monomials). -/
def omicronQuarticChamberRestLF9501810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9501810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * D.natDegree < d)
    (hd1 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF9501810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  simp only [omicronQuarticChamberRestLF9501810PartBCDEFG4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9501810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF9501810 A B C D E F G =
      omicronQuarticChamberRestLF9501810PartBCDEFG1810 A B C D E F G +
        omicronQuarticChamberRestLF9501810PartBCDEFG2810 A B C D E F G +
        omicronQuarticChamberRestLF9501810PartBCDEFG3810 A B C D E F G +
        omicronQuarticChamberRestLF9501810PartBCDEFG4810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticChamberRestLF9501810, omicronQuarticChamberRestLF9501810PartBCDEFG1810, omicronQuarticChamberRestLF9501810PartBCDEFG2810, omicronQuarticChamberRestLF9501810PartBCDEFG3810, omicronQuarticChamberRestLF9501810PartBCDEFG4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF9501810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : 5 * B.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd7 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : 3 * B.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : B.natDegree + 3 * C.natDegree < d)
    (hd11 : A.natDegree + D.natDegree + G.natDegree < d)
    (hd12 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd14 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd15 : B.natDegree + 2 * E.natDegree < d)
    (hd16 : 2 * C.natDegree + F.natDegree < d)
    (hd17 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd18 : 3 * D.natDegree < d)
    (hd19 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  rw [omicronQuarticChamberRestLF9501810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticChamberRestLF9501810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticChamberRestLF9501810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticChamberRestLF9501810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (omicronQuarticChamberRestLF9501810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19))

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRest9501810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl3 : 5 * B.natDegree < d)
    (hl4 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl5 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl6 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl7 : A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl8 : 3 * B.natDegree + E.natDegree < d)
    (hl9 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl10 : B.natDegree + 3 * C.natDegree < d)
    (hl11 : A.natDegree + D.natDegree + G.natDegree < d)
    (hl12 : A.natDegree + E.natDegree + F.natDegree < d)
    (hl13 : B.natDegree + C.natDegree + G.natDegree < d)
    (hl14 : B.natDegree + D.natDegree + F.natDegree < d)
    (hl15 : B.natDegree + 2 * E.natDegree < d)
    (hl16 : 2 * C.natDegree + F.natDegree < d)
    (hl17 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl18 : 3 * D.natDegree < d)
    (hl19 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d)) :
    (omicronQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF9501810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19
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
  simp only [omicronQuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `piQuarticChamberRestLF9503810` on the live set `BCDEFG` (6 monomials). -/
def piQuarticChamberRestLF9503810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF9503810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF9503810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF9503810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `piQuarticChamberRestLF9503810` on the live set `BCDEFG` (6 monomials). -/
def piQuarticChamberRestLF9503810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF9503810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd2 : 3 * B.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + D.natDegree < d) :
    (piQuarticChamberRestLF9503810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF9503810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `piQuarticChamberRestLF9503810` on the live set `BCDEFG` (5 monomials). -/
def piQuarticChamberRestLF9503810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (D ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF9503810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * F.natDegree < d)
    (hd1 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd2 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : 2 * D.natDegree + E.natDegree < d) :
    (piQuarticChamberRestLF9503810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [piQuarticChamberRestLF9503810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF9503810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF9503810 A B C D E F G =
      piQuarticChamberRestLF9503810PartBCDEFG1810 A B C D E F G +
        piQuarticChamberRestLF9503810PartBCDEFG2810 A B C D E F G +
        piQuarticChamberRestLF9503810PartBCDEFG3810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [piQuarticChamberRestLF9503810, piQuarticChamberRestLF9503810PartBCDEFG1810, piQuarticChamberRestLF9503810PartBCDEFG2810, piQuarticChamberRestLF9503810PartBCDEFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
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
    (piQuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  rw [piQuarticChamberRestLF9503810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (piQuarticChamberRestLF9503810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (piQuarticChamberRestLF9503810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (piQuarticChamberRestLF9503810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16))

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hl1 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hl2 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl3 : 4 * B.natDegree + C.natDegree < d)
    (hl4 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hl5 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hl6 : A.natDegree + B.natDegree + D.natDegree + E.natDegree < d)
    (hl7 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl8 : 3 * B.natDegree + F.natDegree < d)
    (hl9 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hl10 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hl11 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl12 : A.natDegree + 2 * F.natDegree < d)
    (hl13 : B.natDegree + D.natDegree + G.natDegree < d)
    (hl14 : B.natDegree + E.natDegree + F.natDegree < d)
    (hl15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hl16 : 2 * D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 3 * A.natDegree + B.natDegree + E.natDegree < d ∧ 3 * A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * A.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + E.natDegree < d ∧ 2 * B.natDegree + C.natDegree + D.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ A.natDegree + E.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d ∧ B.natDegree + D.natDegree + F.natDegree < d ∧ B.natDegree + 2 * E.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d ∧ C.natDegree + D.natDegree + E.natDegree < d ∧ 3 * D.natDegree < d ∧ F.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1
  simp only [piQuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/6 of `primitiveQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9501810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 5 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9501810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/6 of `primitiveQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9501810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 2048 : k)) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd5 : 4 * B.natDegree + D.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9501810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/6 of `primitiveQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9501810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(265 / 2048 : k)) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 2 * A.natDegree + D.natDegree + G.natDegree < d)
    (hd2 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9501810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/6 of `primitiveQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9501810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + 3 * D.natDegree < d)
    (hd2 : 3 * B.natDegree + G.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * C.natDegree + E.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9501810PartBCDEFG4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 5/6 of `primitiveQuarticChamberRestLF9501810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF9501810PartBCDEFG5810
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810PartBCDEFG5810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + 2 * F.natDegree < d)
    (hd5 : C.natDegree + D.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810PartBCDEFG5810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9501810PartBCDEFG5810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 6/6 of `primitiveQuarticChamberRestLF9501810` on the live set `BCDEFG` (3 monomials). -/
def primitiveQuarticChamberRestLF9501810PartBCDEFG6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 8 : k)) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810PartBCDEFG6810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd1 : 2 * D.natDegree + F.natDegree < d)
    (hd2 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810PartBCDEFG6810 A B C D E F G).natDegree < d := by
  simp only [primitiveQuarticChamberRestLF9501810PartBCDEFG6810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF9501810 A B C D E F G =
      primitiveQuarticChamberRestLF9501810PartBCDEFG1810 A B C D E F G +
        primitiveQuarticChamberRestLF9501810PartBCDEFG2810 A B C D E F G +
        primitiveQuarticChamberRestLF9501810PartBCDEFG3810 A B C D E F G +
        primitiveQuarticChamberRestLF9501810PartBCDEFG4810 A B C D E F G +
        primitiveQuarticChamberRestLF9501810PartBCDEFG5810 A B C D E F G +
        primitiveQuarticChamberRestLF9501810PartBCDEFG6810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticChamberRestLF9501810, primitiveQuarticChamberRestLF9501810PartBCDEFG1810, primitiveQuarticChamberRestLF9501810PartBCDEFG2810, primitiveQuarticChamberRestLF9501810PartBCDEFG3810, primitiveQuarticChamberRestLF9501810PartBCDEFG4810, primitiveQuarticChamberRestLF9501810PartBCDEFG5810, primitiveQuarticChamberRestLF9501810PartBCDEFG6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF9501810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 5 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd7 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd11 : 4 * B.natDegree + D.natDegree < d)
    (hd12 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd13 : 2 * A.natDegree + D.natDegree + G.natDegree < d)
    (hd14 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd15 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd16 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd17 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd18 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd19 : A.natDegree + 3 * D.natDegree < d)
    (hd20 : 3 * B.natDegree + G.natDegree < d)
    (hd21 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd22 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd23 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd24 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd25 : 3 * C.natDegree + D.natDegree < d)
    (hd26 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd27 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd28 : B.natDegree + 2 * F.natDegree < d)
    (hd29 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd30 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd31 : 2 * D.natDegree + F.natDegree < d)
    (hd32 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF9501810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF9501810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticChamberRestLF9501810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF9501810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticChamberRestLF9501810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (primitiveQuarticChamberRestLF9501810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21 hd22 hd23)) (primitiveQuarticChamberRestLF9501810PartBCDEFG5810_natDegree_lt A B C D E F G hdpos hd24 hd25 hd26 hd27 hd28 hd29)) (primitiveQuarticChamberRestLF9501810PartBCDEFG6810_natDegree_lt A B C D E F G hdpos hd30 hd31 hd32))

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest9501810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + 5 * B.natDegree < d)
    (hl4 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl5 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl6 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl7 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hl8 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hl9 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl10 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl11 : 4 * B.natDegree + D.natDegree < d)
    (hl12 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl13 : 2 * A.natDegree + D.natDegree + G.natDegree < d)
    (hl14 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hl15 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl16 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hl17 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hl18 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl19 : A.natDegree + 3 * D.natDegree < d)
    (hl20 : 3 * B.natDegree + G.natDegree < d)
    (hl21 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl22 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hl23 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hl24 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl25 : 3 * C.natDegree + D.natDegree < d)
    (hl26 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl27 : B.natDegree + E.natDegree + G.natDegree < d)
    (hl28 : B.natDegree + 2 * F.natDegree < d)
    (hl29 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl30 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl31 : 2 * D.natDegree + F.natDegree < d)
    (hl32 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + B.natDegree + D.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 2 * B.natDegree + C.natDegree + E.natDegree < d ∧ 2 * B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + E.natDegree + G.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ B.natDegree + D.natDegree + G.natDegree < d ∧ B.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest9501810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF9501810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25 hl26 hl27 hl28 hl29 hl30 hl31 hl32
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
  simp only [primitiveQuarticChamberRest9501810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `xiQuarticChamberRestLF9505810` on the live set `BCDEFG` (6 monomials). -/
def xiQuarticChamberRestLF9505810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (15 / 256 : k) • (A * B * C * D)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9505810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF9505810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF9505810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `xiQuarticChamberRestLF9505810` on the live set `BCDEFG` (5 monomials). -/
def xiQuarticChamberRestLF9505810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  - (15 / 128 : k) • (C * D ^ 2)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9505810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : C.natDegree + 2 * D.natDegree < d)
    (hd4 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF9505810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [xiQuarticChamberRestLF9505810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9505810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF9505810 A B C D E F G =
      xiQuarticChamberRestLF9505810PartBCDEFG1810 A B C D E F G +
        xiQuarticChamberRestLF9505810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF9505810, xiQuarticChamberRestLF9505810PartBCDEFG1810, xiQuarticChamberRestLF9505810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF9505810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * B.natDegree + D.natDegree < d)
    (hd4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + G.natDegree < d)
    (hd7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : C.natDegree + 2 * D.natDegree < d)
    (hd10 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF9505810 A B C D E F G).natDegree < d := by
  rw [xiQuarticChamberRestLF9505810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (xiQuarticChamberRestLF9505810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (xiQuarticChamberRestLF9505810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest9505810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hl2 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hl3 : 3 * B.natDegree + D.natDegree < d)
    (hl4 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hl5 : A.natDegree + D.natDegree + F.natDegree < d)
    (hl6 : 2 * B.natDegree + G.natDegree < d)
    (hl7 : B.natDegree + C.natDegree + F.natDegree < d)
    (hl8 : B.natDegree + D.natDegree + E.natDegree < d)
    (hl9 : C.natDegree + 2 * D.natDegree < d)
    (hl10 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest9505810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF9505810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10
  have hc0 : (xiQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩
    · rw [xiQuarticColumnL810_zero]
      simpa using hdpos
    · exact xiQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16
  have hc1 : (xiQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [xiQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc2 : (xiQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [xiQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact xiQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc3 : (xiQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [xiQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc4 : (xiQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3⟩
    · rw [xiQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3
  have hc5 : (xiQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [xiQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2
  have hc6 : (xiQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [xiQuarticColumnEta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1
  have hc7 : (xiQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [xiQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact xiQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0
  simp only [xiQuarticChamberRest9505810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree < d)
    (hd3 : B.natDegree + G.natDegree < d) :
    (kappaQuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [kappaQuarticChamberRestLF9503810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + D.natDegree < d)
    (hl2 : B.natDegree + 2 * C.natDegree < d)
    (hl3 : B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3
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
  simp only [kappaQuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d)
    (hd2 : 2 * B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + 2 * D.natDegree < d) :
    (n2QuarticChamberRestLF9503810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n2QuarticChamberRestLF9503810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberRest9503810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : 3 * B.natDegree + C.natDegree < d)
    (hl2 : 2 * B.natDegree + F.natDegree < d)
    (hl3 : B.natDegree + C.natDegree + E.natDegree < d)
    (hl4 : B.natDegree + 2 * D.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * B.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (n2QuarticChamberRest9503810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n2QuarticChamberRestLF9503810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4
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
  simp only [n2QuarticChamberRest9503810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `n3QuarticChamberRestLF9504810` on the live set `BCDEFG` (6 monomials). -/
def n3QuarticChamberRestLF9504810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 8192 : k)) • (A ^ 2 * B ^ 2 * D)
  - (175 / 8192 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (65 / 2048 : k) • (A * B ^ 2 * F)
  + (45 / 1024 : k) • (A * B * C * E)
  + (85 / 2048 : k) • (A * B * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9504810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : 5 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * D.natDegree < d) :
    (n3QuarticChamberRestLF9504810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [n3QuarticChamberRestLF9504810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `n3QuarticChamberRestLF9504810` on the live set `BCDEFG` (6 monomials). -/
def n3QuarticChamberRestLF9504810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9504810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + E.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : B.natDegree + 3 * C.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd4 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + 2 * E.natDegree < d) :
    (n3QuarticChamberRestLF9504810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [n3QuarticChamberRestLF9504810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `n3QuarticChamberRestLF9504810` on the live set `BCDEFG` (4 monomials). -/
def n3QuarticChamberRestLF9504810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 : k)) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9504810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * C.natDegree + F.natDegree < d)
    (hd1 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 3 * D.natDegree < d)
    (hd3 : F.natDegree + G.natDegree < d) :
    (n3QuarticChamberRestLF9504810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [n3QuarticChamberRestLF9504810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9504810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    n3QuarticChamberRestLF9504810 A B C D E F G =
      n3QuarticChamberRestLF9504810PartBCDEFG1810 A B C D E F G +
        n3QuarticChamberRestLF9504810PartBCDEFG2810 A B C D E F G +
        n3QuarticChamberRestLF9504810PartBCDEFG3810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n3QuarticChamberRestLF9504810, n3QuarticChamberRestLF9504810PartBCDEFG1810, n3QuarticChamberRestLF9504810PartBCDEFG2810, n3QuarticChamberRestLF9504810PartBCDEFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRestLF9504810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : 5 * B.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd6 : 3 * B.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + 3 * C.natDegree < d)
    (hd9 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd10 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd11 : B.natDegree + 2 * E.natDegree < d)
    (hd12 : 2 * C.natDegree + F.natDegree < d)
    (hd13 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd14 : 3 * D.natDegree < d)
    (hd15 : F.natDegree + G.natDegree < d) :
    (n3QuarticChamberRestLF9504810 A B C D E F G).natDegree < d := by
  rw [n3QuarticChamberRestLF9504810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n3QuarticChamberRestLF9504810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n3QuarticChamberRestLF9504810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n3QuarticChamberRestLF9504810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15))

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberRest9504810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl2 : 5 * B.natDegree < d)
    (hl3 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl4 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl5 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl6 : 3 * B.natDegree + E.natDegree < d)
    (hl7 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl8 : B.natDegree + 3 * C.natDegree < d)
    (hl9 : B.natDegree + C.natDegree + G.natDegree < d)
    (hl10 : B.natDegree + D.natDegree + F.natDegree < d)
    (hl11 : B.natDegree + 2 * E.natDegree < d)
    (hl12 : 2 * C.natDegree + F.natDegree < d)
    (hl13 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl14 : 3 * D.natDegree < d)
    (hl15 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d)) :
    (n3QuarticChamberRest9504810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n3QuarticChamberRestLF9504810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15
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
  simp only [n3QuarticChamberRest9504810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/5 of `n4QuarticChamberRestLF9505810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9505810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 3 * B ^ 2 * D)
  + (155 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (107 / 8192 : k) • (A * B ^ 5)
  - (55 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (95 / 2048 : k) • (A ^ 2 * B * D ^ 2)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 5 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d) :
    (n4QuarticChamberRestLF9505810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9505810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/5 of `n4QuarticChamberRestLF9505810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9505810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(45 / 512 : k)) • (A * B ^ 3 * E)
  - (135 / 512 : k) • (A * B ^ 2 * C * D)
  - (15 / 256 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 32 : k) • (A * B * C * G)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd3 : 4 * B.natDegree + D.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d) :
    (n4QuarticChamberRestLF9505810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9505810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/5 of `n4QuarticChamberRestLF9505810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9505810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (A * B * D * F)
  + (5 / 32 : k) • (A * B * E ^ 2)
  + (5 / 64 : k) • (A * C ^ 2 * F)
  + (5 / 16 : k) • (A * C * D * E)
  + (5 / 64 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd2 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + 3 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + G.natDegree < d) :
    (n4QuarticChamberRestLF9505810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9505810PartBCDEFG3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/5 of `n4QuarticChamberRestLF9505810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9505810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 8 : k) • (A * F * G)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd4 : 3 * C.natDegree + D.natDegree < d)
    (hd5 : A.natDegree + F.natDegree + G.natDegree < d) :
    (n4QuarticChamberRestLF9505810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9505810PartBCDEFG4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 5/5 of `n4QuarticChamberRestLF9505810` on the live set `BCDEFG` (6 monomials). -/
def n4QuarticChamberRestLF9505810PartBCDEFG5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810PartBCDEFG5810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + 2 * F.natDegree < d)
    (hd2 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd3 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd4 : 2 * D.natDegree + F.natDegree < d)
    (hd5 : D.natDegree + 2 * E.natDegree < d) :
    (n4QuarticChamberRestLF9505810PartBCDEFG5810 A B C D E F G).natDegree < d := by
  simp only [n4QuarticChamberRestLF9505810PartBCDEFG5810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    n4QuarticChamberRestLF9505810 A B C D E F G =
      n4QuarticChamberRestLF9505810PartBCDEFG1810 A B C D E F G +
        n4QuarticChamberRestLF9505810PartBCDEFG2810 A B C D E F G +
        n4QuarticChamberRestLF9505810PartBCDEFG3810 A B C D E F G +
        n4QuarticChamberRestLF9505810PartBCDEFG4810 A B C D E F G +
        n4QuarticChamberRestLF9505810PartBCDEFG5810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [n4QuarticChamberRestLF9505810, n4QuarticChamberRestLF9505810PartBCDEFG1810, n4QuarticChamberRestLF9505810PartBCDEFG2810, n4QuarticChamberRestLF9505810PartBCDEFG3810, n4QuarticChamberRestLF9505810PartBCDEFG4810, n4QuarticChamberRestLF9505810PartBCDEFG5810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRestLF9505810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 5 * B.natDegree < d)
    (hd3 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd4 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd6 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd8 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd9 : 4 * B.natDegree + D.natDegree < d)
    (hd10 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd12 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd14 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd15 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd16 : A.natDegree + 3 * D.natDegree < d)
    (hd17 : 3 * B.natDegree + G.natDegree < d)
    (hd18 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd19 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd20 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd21 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd22 : 3 * C.natDegree + D.natDegree < d)
    (hd23 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd24 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd25 : B.natDegree + 2 * F.natDegree < d)
    (hd26 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd27 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd28 : 2 * D.natDegree + F.natDegree < d)
    (hd29 : D.natDegree + 2 * E.natDegree < d) :
    (n4QuarticChamberRestLF9505810 A B C D E F G).natDegree < d := by
  rw [n4QuarticChamberRestLF9505810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n4QuarticChamberRestLF9505810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (n4QuarticChamberRestLF9505810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (n4QuarticChamberRestLF9505810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (n4QuarticChamberRestLF9505810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21 hd22 hd23)) (n4QuarticChamberRestLF9505810PartBCDEFG5810_natDegree_lt A B C D E F G hdpos hd24 hd25 hd26 hd27 hd28 hd29))

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberRest9505810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + 5 * B.natDegree < d)
    (hl3 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl4 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl5 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl6 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hl7 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl8 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl9 : 4 * B.natDegree + D.natDegree < d)
    (hl10 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl11 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl12 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hl13 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hl14 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hl15 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl16 : A.natDegree + 3 * D.natDegree < d)
    (hl17 : 3 * B.natDegree + G.natDegree < d)
    (hl18 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl19 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hl20 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hl21 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl22 : 3 * C.natDegree + D.natDegree < d)
    (hl23 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl24 : B.natDegree + E.natDegree + G.natDegree < d)
    (hl25 : B.natDegree + 2 * F.natDegree < d)
    (hl26 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl27 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl28 : 2 * D.natDegree + F.natDegree < d)
    (hl29 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + B.natDegree + D.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 2 * B.natDegree + C.natDegree + E.natDegree < d ∧ 2 * B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ B.natDegree + D.natDegree + G.natDegree < d ∧ B.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (n4QuarticChamberRest9505810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    n4QuarticChamberRestLF9505810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25 hl26 hl27 hl28 hl29
  have hc0 : (n4QuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37⟩
    · rw [n4QuarticColumnL1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL1810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc1 : (n4QuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37⟩
    · rw [n4QuarticColumnL2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnL2810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 g32 g33 g34 g35 g36 g37
  have hc2 : (n4QuarticColumnBeta1810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21⟩
    · rw [n4QuarticColumnBeta1810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta1810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19
  have hc3 : (n4QuarticColumnBeta2810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21⟩
    · rw [n4QuarticColumnBeta2810_zero]
      simpa using hdpos
    · exact n4QuarticColumnBeta2810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g20 g21
  have hc4 : (n4QuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩
    · rw [n4QuarticColumnGamma810_zero]
      simpa using hdpos
    · exact n4QuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
  have hc5 : (n4QuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩
    · rw [n4QuarticColumnDelta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have hc6 : (n4QuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [n4QuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc7 : (n4QuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [n4QuarticColumnZeta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc8 : (n4QuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n4QuarticColumnEta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc9 : (n4QuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [n4QuarticColumnTheta810_zero]
      simpa using hdpos
    · exact n4QuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  simp only [n4QuarticChamberRest9505810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticChamberRestLF9502810` on the live set `BCDEFG` (6 monomials). -/
def nuQuarticChamberRestLF9502810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (15 / 1024 : k) • (A * B * C ^ 2)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * B * G)
  - (15 / 128 : k) • (B ^ 2 * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9502810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd5 : 2 * B.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF9502810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  simp only [nuQuarticChamberRestLF9502810PartBCDEFG1810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticChamberRestLF9502810` on the live set `BCDEFG` (5 monomials). -/
def nuQuarticChamberRestLF9502810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 64 : k)) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9502810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd1 : B.natDegree + 2 * D.natDegree < d)
    (hd2 : 2 * C.natDegree + D.natDegree < d)
    (hd3 : D.natDegree + G.natDegree < d)
    (hd4 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF9502810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  simp only [nuQuarticChamberRestLF9502810PartBCDEFG2810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9502810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF9502810 A B C D E F G =
      nuQuarticChamberRestLF9502810PartBCDEFG1810 A B C D E F G +
        nuQuarticChamberRestLF9502810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticChamberRestLF9502810, nuQuarticChamberRestLF9502810PartBCDEFG1810, nuQuarticChamberRestLF9502810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + G.natDegree < d)
    (hd5 : 2 * B.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : B.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * C.natDegree + D.natDegree < d)
    (hd9 : D.natDegree + G.natDegree < d)
    (hd10 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF9502810 A B C D E F G).natDegree < d := by
  rw [nuQuarticChamberRestLF9502810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (nuQuarticChamberRestLF9502810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticChamberRestLF9502810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10))

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRest9502810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hl3 : 3 * B.natDegree + C.natDegree < d)
    (hl4 : A.natDegree + B.natDegree + G.natDegree < d)
    (hl5 : 2 * B.natDegree + F.natDegree < d)
    (hl6 : B.natDegree + C.natDegree + E.natDegree < d)
    (hl7 : B.natDegree + 2 * D.natDegree < d)
    (hl8 : 2 * C.natDegree + D.natDegree < d)
    (hl9 : D.natDegree + G.natDegree < d)
    (hl10 : E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest9502810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF9502810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10
  have hc0 : (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩
    · rw [nuQuarticColumnL810_zero]
      simpa using hdpos
    · exact nuQuarticColumnL810_natDegree_lt_of_live_BCDEFG l A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
  have hc1 : (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [nuQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnBeta810_natDegree_lt_of_live_BCDEFG beta A B C D E F G hdpos g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc2 : (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [nuQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact nuQuarticColumnGamma810_natDegree_lt_of_live_BCDEFG gamma A B C D E F G hdpos g0 g1 g2 g3 g4
  have hc3 : (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [nuQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnDelta810_natDegree_lt_of_live_BCDEFG delta A B C D E F G hdpos g0 g1 g2 g3 g4 g5
  have hc4 : (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCDEFG epsilon A B C D E F G hdpos g0 g1 g2
  have hc5 : (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnZeta810_natDegree_lt_of_live_BCDEFG zeta A B C D E F G hdpos g0 g1 g2
  have hc6 : (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnEta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEta810_natDegree_lt_of_live_BCDEFG eta A B C D E F G hdpos g0 g1
  have hc7 : (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnTheta810_natDegree_lt_of_live_BCDEFG theta A B C D E F G hdpos g0 g1
  simp only [nuQuarticChamberRest9502810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7


end QuarticChamberUnownedTreeRests3810

end Max11DegreeRoutes
