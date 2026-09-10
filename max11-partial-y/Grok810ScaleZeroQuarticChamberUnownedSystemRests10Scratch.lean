import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns8Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns9Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns10Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemRests9Scratch
import Max11SpeedReflectDegLibScratch

/-! # UnownedSystem chamber rests, part 10/11

25 of the 180 load-free and 180 full (packet,
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

section QuarticChamberUnownedSystemRests10810

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + D.natDegree < d)
    (hl2 : D.natDegree + E.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2
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
  simp only [kappaQuarticChamberRest6006810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def nuQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * D * E)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6006810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (35 / 512 : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6006810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + E.natDegree < d) :
    (nuQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6006810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticChamberRestLF6006810` on the live set `BCDEFG` (2 monomials). -/
def nuQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6006810PartBCDEFG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6006810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * D.natDegree < d)
    (hd1 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6006810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6006810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6006810 A B C D E F G =
      nuQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G +
        nuQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticChamberRestLF6006810, nuQuarticChamberRestLF6006810PartBCDEFG1810, nuQuarticChamberRestLF6006810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : B.natDegree + 2 * D.natDegree < d)
    (hd7 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6006810 A B C D E F G).natDegree < d := by
  rw [nuQuarticChamberRestLF6006810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (nuQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRest6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 3 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + D.natDegree + E.natDegree < d)
    (hl4 : 2 * B.natDegree + F.natDegree < d)
    (hl5 : B.natDegree + C.natDegree + E.natDegree < d)
    (hl6 : B.natDegree + 2 * D.natDegree < d)
    (hl7 : E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
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
  simp only [nuQuarticChamberRest6006810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `xiQuarticChamberRestLF6004810` on the live set `BCDEFG` (6 monomials). -/
def xiQuarticChamberRestLF6004810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6004810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6004810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6004810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF6004810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6004810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF6004810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6004810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `xiQuarticChamberRestLF6004810` on the live set `BCDEFG` (4 monomials). -/
def xiQuarticChamberRestLF6004810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 128 : k)) • (B * D * E)
  - (15 / 128 : k) • (C ^ 2 * E)
  + (5 / 16 : k) • (E * G)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6004810PartBCDEFG2810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6004810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6004810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF6004810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6004810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 2 * C.natDegree + E.natDegree < d)
    (hd2 : E.natDegree + G.natDegree < d)
    (hd3 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF6004810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6004810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6004810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6004810 A B C D E F G =
      xiQuarticChamberRestLF6004810PartBCDEFG1810 A B C D E F G +
        xiQuarticChamberRestLF6004810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF6004810, xiQuarticChamberRestLF6004810PartBCDEFG1810, xiQuarticChamberRestLF6004810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6004810_natDegree_lt_of_live_BCDEFG
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
    (hd8 : E.natDegree + G.natDegree < d)
    (hd9 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF6004810 A B C D E F G).natDegree < d := by
  rw [xiQuarticChamberRestLF6004810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (xiQuarticChamberRestLF6004810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (xiQuarticChamberRestLF6004810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest6004810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hl2 : 3 * B.natDegree + D.natDegree < d)
    (hl3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hl4 : 2 * B.natDegree + G.natDegree < d)
    (hl5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hl6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hl7 : 2 * C.natDegree + E.natDegree < d)
    (hl8 : E.natDegree + G.natDegree < d)
    (hl9 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF6004810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9
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
  simp only [xiQuarticChamberRest6004810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/4 of `omicronQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  - (5 / 2048 : k) • (A ^ 2 * D * E)
  + (25 / 1024 : k) • (A * B ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6006810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(45 / 16384) : k), (-(35 / 2048) : k),
      (-(21 / 4096) : k), (-(5 / 2048) : k), (25 / 1024 : k)
      ]
      [
      [3, 3, 0, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0],
      [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0]
      ] := by
  simp only [omicronQuarticChamberRestLF6006810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : 5 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + F.natDegree < d) :
    (omicronQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/4 of `omicronQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B * C * E)
  + (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6006810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 1024 : k), (5 / 128 : k),
      (135 / 1024 : k), (45 / 1024 : k), (-(5 / 128) : k)
      ]
      [
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0],
      [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [omicronQuarticChamberRestLF6006810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd2 : 3 * B.natDegree + E.natDegree < d)
    (hd3 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : B.natDegree + 3 * C.natDegree < d)
    (hd5 : A.natDegree + E.natDegree + F.natDegree < d) :
    (omicronQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/4 of `omicronQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF6006810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6006810PartBCDEFG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG3810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6006810PartBCDEFG3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(5 / 32) : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(5 / 128) : k)
      ]
      [
      [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0],
      [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0]
      ] := by
  simp only [omicronQuarticChamberRestLF6006810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6006810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd2 : B.natDegree + 2 * E.natDegree < d)
    (hd3 : 2 * C.natDegree + F.natDegree < d)
    (hd4 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 3 * D.natDegree < d) :
    (omicronQuarticChamberRestLF6006810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/4 of `omicronQuarticChamberRestLF6006810` on the live set `BCDEFG` (1 monomials). -/
def omicronQuarticChamberRestLF6006810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6006810PartBCDEFG4810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG4810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6006810PartBCDEFG4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k)
      ]
      [
      [0, 0, 0, 0, 0, 1, 1]
      ] := by
  simp only [omicronQuarticChamberRestLF6006810PartBCDEFG4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6006810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF6006810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6006810PartBCDEFG4810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6006810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6006810 A B C D E F G =
      omicronQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G +
        omicronQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G +
        omicronQuarticChamberRestLF6006810PartBCDEFG3810 A B C D E F G +
        omicronQuarticChamberRestLF6006810PartBCDEFG4810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticChamberRestLF6006810, omicronQuarticChamberRestLF6006810PartBCDEFG1810, omicronQuarticChamberRestLF6006810PartBCDEFG2810, omicronQuarticChamberRestLF6006810PartBCDEFG3810, omicronQuarticChamberRestLF6006810PartBCDEFG4810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : 5 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd8 : 3 * B.natDegree + E.natDegree < d)
    (hd9 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : B.natDegree + 3 * C.natDegree < d)
    (hd11 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd12 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd14 : B.natDegree + 2 * E.natDegree < d)
    (hd15 : 2 * C.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd17 : 3 * D.natDegree < d)
    (hd18 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF6006810 A B C D E F G).natDegree < d := by
  rw [omicronQuarticChamberRestLF6006810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticChamberRestLF6006810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (omicronQuarticChamberRestLF6006810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18))

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRest6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl3 : 5 * B.natDegree < d)
    (hl4 : 2 * A.natDegree + D.natDegree + E.natDegree < d)
    (hl5 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl6 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl7 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl8 : 3 * B.natDegree + E.natDegree < d)
    (hl9 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl10 : B.natDegree + 3 * C.natDegree < d)
    (hl11 : A.natDegree + E.natDegree + F.natDegree < d)
    (hl12 : B.natDegree + C.natDegree + G.natDegree < d)
    (hl13 : B.natDegree + D.natDegree + F.natDegree < d)
    (hl14 : B.natDegree + 2 * E.natDegree < d)
    (hl15 : 2 * C.natDegree + F.natDegree < d)
    (hl16 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl17 : 3 * D.natDegree < d)
    (hl18 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d)) :
    (omicronQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18
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
  simp only [omicronQuarticChamberRest6006810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/6 of `primitiveQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6006810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(15 / 16384) : k), (15 / 8192 : k),
      (65 / 8192 : k), (-(5 / 2048) : k), (-(5 / 2048) : k)
      ]
      [
      [4, 3, 0, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [3, 0, 0, 1, 1, 0, 0], [2, 2, 0, 0, 0, 1, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6006810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 5 * B.natDegree < d)
    (hd4 : 3 * A.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/6 of `primitiveQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6006810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 1024 : k), (-(25 / 2048) : k), (-(25 / 512) : k),
      (-(135 / 1024) : k), (-(15 / 1024) : k), (-(125 / 2048) : k)
      ]
      [
      [2, 1, 1, 0, 1, 0, 0], [2, 1, 0, 2, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 2, 1, 1, 0, 0, 0],
      [1, 1, 3, 0, 0, 0, 0], [0, 4, 0, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6006810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd1 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd5 : 4 * B.natDegree + D.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/6 of `primitiveQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6006810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(265 / 2048 : k)) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6006810PartBCDEFG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG3810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810PartBCDEFG3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(265 / 2048) : k), (-(5 / 256) : k), (5 / 128 : k),
      (5 / 32 : k), (5 / 64 : k), (15 / 128 : k)
      ]
      [
      [0, 3, 2, 0, 0, 0, 0], [2, 0, 0, 0, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1, 0],
      [1, 1, 0, 0, 2, 0, 0], [1, 0, 1, 1, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6006810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd4 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd5 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/6 of `primitiveQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6006810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6006810PartBCDEFG4810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG4810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810PartBCDEFG4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 128 : k), (15 / 256 : k), (85 / 256 : k),
      (85 / 256 : k), (45 / 128 : k), (45 / 128 : k)
      ]
      [
      [1, 0, 0, 3, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 1, 0], [0, 2, 0, 1, 1, 0, 0],
      [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6006810PartBCDEFG4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * D.natDegree < d)
    (hd1 : 3 * B.natDegree + G.natDegree < d)
    (hd2 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG4810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 5/6 of `primitiveQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6006810PartBCDEFG5810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6006810PartBCDEFG5810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG5810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810PartBCDEFG5810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 128 : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (-(5 / 8) : k)
      ]
      [
      [0, 0, 3, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 2, 0],
      [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6006810PartBCDEFG5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810PartBCDEFG5810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * C.natDegree + D.natDegree < d)
    (hd1 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd2 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd3 : B.natDegree + 2 * F.natDegree < d)
    (hd4 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd5 : C.natDegree + E.natDegree + F.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810PartBCDEFG5810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG5810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 6/6 of `primitiveQuarticChamberRestLF6006810` on the live set `BCDEFG` (2 monomials). -/
def primitiveQuarticChamberRestLF6006810PartBCDEFG6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6006810PartBCDEFG6810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG6810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810PartBCDEFG6810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 16) : k)
      ]
      [
      [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6006810PartBCDEFG6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810PartBCDEFG6810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * D.natDegree + F.natDegree < d)
    (hd1 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810PartBCDEFG6810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6006810PartBCDEFG6810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6006810 A B C D E F G =
      primitiveQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G +
        primitiveQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G +
        primitiveQuarticChamberRestLF6006810PartBCDEFG3810 A B C D E F G +
        primitiveQuarticChamberRestLF6006810PartBCDEFG4810 A B C D E F G +
        primitiveQuarticChamberRestLF6006810PartBCDEFG5810 A B C D E F G +
        primitiveQuarticChamberRestLF6006810PartBCDEFG6810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticChamberRestLF6006810, primitiveQuarticChamberRestLF6006810PartBCDEFG1810, primitiveQuarticChamberRestLF6006810PartBCDEFG2810, primitiveQuarticChamberRestLF6006810PartBCDEFG3810, primitiveQuarticChamberRestLF6006810PartBCDEFG4810, primitiveQuarticChamberRestLF6006810PartBCDEFG5810, primitiveQuarticChamberRestLF6006810PartBCDEFG6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 5 * B.natDegree < d)
    (hd4 : 3 * A.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd8 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd9 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd10 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd11 : 4 * B.natDegree + D.natDegree < d)
    (hd12 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd13 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd15 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd17 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd18 : A.natDegree + 3 * D.natDegree < d)
    (hd19 : 3 * B.natDegree + G.natDegree < d)
    (hd20 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd21 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd22 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd23 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd24 : 3 * C.natDegree + D.natDegree < d)
    (hd25 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd26 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd27 : B.natDegree + 2 * F.natDegree < d)
    (hd28 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd29 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd30 : 2 * D.natDegree + F.natDegree < d)
    (hd31 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF6006810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF6006810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticChamberRestLF6006810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (primitiveQuarticChamberRestLF6006810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21 hd22 hd23)) (primitiveQuarticChamberRestLF6006810PartBCDEFG5810_natDegree_lt A B C D E F G hdpos hd24 hd25 hd26 hd27 hd28 hd29)) (primitiveQuarticChamberRestLF6006810PartBCDEFG6810_natDegree_lt A B C D E F G hdpos hd30 hd31))

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + 5 * B.natDegree < d)
    (hl4 : 3 * A.natDegree + D.natDegree + E.natDegree < d)
    (hl5 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl6 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d)
    (hl7 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hl8 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hl9 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl10 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl11 : 4 * B.natDegree + D.natDegree < d)
    (hl12 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl13 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hl14 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl15 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hl16 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hl17 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl18 : A.natDegree + 3 * D.natDegree < d)
    (hl19 : 3 * B.natDegree + G.natDegree < d)
    (hl20 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl21 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hl22 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hl23 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl24 : 3 * C.natDegree + D.natDegree < d)
    (hl25 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl26 : B.natDegree + E.natDegree + G.natDegree < d)
    (hl27 : B.natDegree + 2 * F.natDegree < d)
    (hl28 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl29 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl30 : 2 * D.natDegree + F.natDegree < d)
    (hl31 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + B.natDegree + D.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 2 * B.natDegree + C.natDegree + E.natDegree < d ∧ 2 * B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + E.natDegree + G.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ B.natDegree + D.natDegree + G.natDegree < d ∧ B.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25 hl26 hl27 hl28 hl29 hl30 hl31
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
  simp only [primitiveQuarticChamberRest6006810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF6008810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_kappaQuarticChamberRestLF6008810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF6008810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF6008810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d) :
    (kappaQuarticChamberRestLF6008810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemRests10_kappaQuarticChamberRestLF6008810]
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
theorem kappaQuarticChamberRest6008810_natDegree_lt_of_live_BCDEFG
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
    (kappaQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
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
  simp only [kappaQuarticChamberRest6008810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def nuQuarticChamberRestLF6008810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6008810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6008810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (35 / 512 : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (-(15 / 128) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0],
      [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6008810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6008810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d) :
    (nuQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6008810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticChamberRestLF6008810` on the live set `BCDEFG` (1 monomials). -/
def nuQuarticChamberRestLF6008810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6008810PartBCDEFG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6008810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 16 : k)
      ]
      [
      [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6008810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6008810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6008810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6008810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6008810 A B C D E F G =
      nuQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G +
        nuQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticChamberRestLF6008810, nuQuarticChamberRestLF6008810PartBCDEFG1810, nuQuarticChamberRestLF6008810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : 2 * B.natDegree + F.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd5 : B.natDegree + 2 * D.natDegree < d)
    (hd6 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6008810 A B C D E F G).natDegree < d := by
  rw [nuQuarticChamberRestLF6008810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (nuQuarticChamberRestLF6008810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticChamberRestLF6008810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6))

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRest6008810_natDegree_lt_of_live_BCDEFG
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
    (hl6 : E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6
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
  simp only [nuQuarticChamberRest6008810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `xiQuarticChamberRestLF6006810` on the live set `BCDEFG` (6 monomials). -/
def xiQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (B ^ 2 * G)
  - (25 / 128 : k) • (B * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6006810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6006810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0]
      ] := by
  simp only [xiQuarticChamberRestLF6006810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * B.natDegree + G.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + F.natDegree < d) :
    (xiQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6006810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `xiQuarticChamberRestLF6006810` on the live set `BCDEFG` (2 monomials). -/
def xiQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 128 : k)) • (B * D * E)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6006810PartBCDEFG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6006810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF6006810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd1 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6006810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6006810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6006810 A B C D E F G =
      xiQuarticChamberRestLF6006810PartBCDEFG1810 A B C D E F G +
        xiQuarticChamberRestLF6006810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF6006810, xiQuarticChamberRestLF6006810PartBCDEFG1810, xiQuarticChamberRestLF6006810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
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
    (hd7 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF6006810 A B C D E F G).natDegree < d := by
  rw [xiQuarticChamberRestLF6006810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (xiQuarticChamberRestLF6006810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (xiQuarticChamberRestLF6006810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest6006810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hl2 : 3 * B.natDegree + D.natDegree < d)
    (hl3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hl4 : 2 * B.natDegree + G.natDegree < d)
    (hl5 : B.natDegree + C.natDegree + F.natDegree < d)
    (hl6 : B.natDegree + D.natDegree + E.natDegree < d)
    (hl7 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest6006810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF6006810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
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
  simp only [xiQuarticChamberRest6006810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/3 of `omicronQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF6008810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 3 * B ^ 3)
  - (45 / 16384 : k) • (A ^ 2 * B ^ 2 * D)
  - (35 / 2048 : k) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (25 / 1024 : k) • (A * B ^ 2 * F)
  + (15 / 512 : k) • (A * B * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6008810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6008810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(45 / 16384) : k), (-(35 / 2048) : k),
      (-(21 / 4096) : k), (25 / 1024 : k), (15 / 512 : k)
      ]
      [
      [3, 3, 0, 0, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0]
      ] := by
  simp only [omicronQuarticChamberRestLF6008810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6008810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : 5 * B.natDegree < d)
    (hd4 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + E.natDegree < d) :
    (omicronQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6008810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/3 of `omicronQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF6008810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 1024 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (5 / 128 : k) • (A * E * F)
  - (15 / 128 : k) • (B * C * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6008810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6008810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 1024 : k), (5 / 128 : k), (135 / 1024 : k),
      (45 / 1024 : k), (-(5 / 128) : k), (-(15 / 128) : k)
      ]
      [
      [1, 1, 0, 2, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1]
      ] := by
  simp only [omicronQuarticChamberRestLF6008810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6008810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd1 : 3 * B.natDegree + E.natDegree < d)
    (hd2 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : B.natDegree + 3 * C.natDegree < d)
    (hd4 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6008810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/3 of `omicronQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def omicronQuarticChamberRestLF6008810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 32 : k)) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6008810PartBCDEFG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6008810PartBCDEFG3810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6008810PartBCDEFG3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 32) : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(5 / 128) : k), (5 / 16 : k)
      ]
      [
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1]
      ] := by
  simp only [omicronQuarticChamberRestLF6008810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6008810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd1 : B.natDegree + 2 * E.natDegree < d)
    (hd2 : 2 * C.natDegree + F.natDegree < d)
    (hd3 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd4 : 3 * D.natDegree < d)
    (hd5 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF6008810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_omicronQuarticChamberRestLF6008810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6008810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6008810 A B C D E F G =
      omicronQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G +
        omicronQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G +
        omicronQuarticChamberRestLF6008810PartBCDEFG3810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [omicronQuarticChamberRestLF6008810, omicronQuarticChamberRestLF6008810PartBCDEFG1810, omicronQuarticChamberRestLF6008810PartBCDEFG2810, omicronQuarticChamberRestLF6008810PartBCDEFG3810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
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
    (hd7 : 3 * B.natDegree + E.natDegree < d)
    (hd8 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd9 : B.natDegree + 3 * C.natDegree < d)
    (hd10 : A.natDegree + E.natDegree + F.natDegree < d)
    (hd11 : B.natDegree + C.natDegree + G.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + F.natDegree < d)
    (hd13 : B.natDegree + 2 * E.natDegree < d)
    (hd14 : 2 * C.natDegree + F.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + E.natDegree < d)
    (hd16 : 3 * D.natDegree < d)
    (hd17 : F.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF6008810 A B C D E F G).natDegree < d := by
  rw [omicronQuarticChamberRestLF6008810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (omicronQuarticChamberRestLF6008810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (omicronQuarticChamberRestLF6008810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (omicronQuarticChamberRestLF6008810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17))

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRest6008810_natDegree_lt_of_live_BCDEFG
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
    (hl7 : 3 * B.natDegree + E.natDegree < d)
    (hl8 : 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl9 : B.natDegree + 3 * C.natDegree < d)
    (hl10 : A.natDegree + E.natDegree + F.natDegree < d)
    (hl11 : B.natDegree + C.natDegree + G.natDegree < d)
    (hl12 : B.natDegree + D.natDegree + F.natDegree < d)
    (hl13 : B.natDegree + 2 * E.natDegree < d)
    (hl14 : 2 * C.natDegree + F.natDegree < d)
    (hl15 : C.natDegree + D.natDegree + E.natDegree < d)
    (hl16 : 3 * D.natDegree < d)
    (hl17 : F.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ E.natDegree + G.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d)) :
    (omicronQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17
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
  simp only [omicronQuarticChamberRest6008810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/6 of `primitiveQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6008810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6008810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 65536) : k), (-(15 / 16384) : k), (15 / 8192 : k),
      (65 / 8192 : k), (-(5 / 2048) : k), (15 / 1024 : k)
      ]
      [
      [4, 3, 0, 0, 0, 0, 0], [3, 2, 0, 1, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 1, 0], [2, 1, 1, 0, 1, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6008810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 4 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : 3 * A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + 5 * B.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd5 : 2 * A.natDegree + B.natDegree + C.natDegree + E.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/6 of `primitiveQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6008810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 2048 : k)) • (A ^ 2 * B * D ^ 2)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6008810PartBCDEFG2810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 2048) : k), (-(25 / 512) : k), (-(135 / 1024) : k),
      (-(15 / 1024) : k), (-(125 / 2048) : k), (-(265 / 2048) : k)
      ]
      [
      [2, 1, 0, 2, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 2, 1, 1, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0],
      [0, 4, 0, 1, 0, 0, 0], [0, 3, 2, 0, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6008810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + B.natDegree + 2 * D.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 4 * B.natDegree + D.natDegree < d)
    (hd5 : 3 * B.natDegree + 2 * C.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 3/6 of `primitiveQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6008810PartBCDEFG3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 256 : k)) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6008810PartBCDEFG3810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG3810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810PartBCDEFG3810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 256) : k), (5 / 128 : k), (5 / 32 : k),
      (5 / 64 : k), (15 / 128 : k), (5 / 128 : k)
      ]
      [
      [2, 0, 0, 0, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 2, 0, 0],
      [1, 0, 1, 1, 1, 0, 0], [1, 0, 0, 3, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6008810PartBCDEFG3810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810PartBCDEFG3810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd5 : A.natDegree + 3 * D.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810PartBCDEFG3810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG3810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 4/6 of `primitiveQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6008810PartBCDEFG4810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6008810PartBCDEFG4810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG4810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810PartBCDEFG4810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 256 : k), (85 / 256 : k), (85 / 256 : k),
      (45 / 128 : k), (45 / 128 : k), (15 / 128 : k)
      ]
      [
      [0, 3, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 1, 0], [0, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 0, 0],
      [0, 1, 1, 2, 0, 0, 0], [0, 0, 3, 1, 0, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6008810PartBCDEFG4810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810PartBCDEFG4810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + G.natDegree < d)
    (hd1 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd2 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd3 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * C.natDegree + D.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810PartBCDEFG4810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG4810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 5/6 of `primitiveQuarticChamberRestLF6008810` on the live set `BCDEFG` (6 monomials). -/
def primitiveQuarticChamberRestLF6008810PartBCDEFG5810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6008810PartBCDEFG5810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG5810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810PartBCDEFG5810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(5 / 16) : k)
      ]
      [
      [1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 2, 0], [0, 0, 1, 1, 0, 0, 1],
      [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 0, 1, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6008810PartBCDEFG5810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810PartBCDEFG5810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd1 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd2 : B.natDegree + 2 * F.natDegree < d)
    (hd3 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd4 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd5 : 2 * D.natDegree + F.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810PartBCDEFG5810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG5810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 6/6 of `primitiveQuarticChamberRestLF6008810` on the live set `BCDEFG` (1 monomials). -/
def primitiveQuarticChamberRestLF6008810PartBCDEFG6810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6008810PartBCDEFG6810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG6810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810PartBCDEFG6810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k)
      ]
      [
      [0, 0, 0, 1, 2, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6008810PartBCDEFG6810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810PartBCDEFG6810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810PartBCDEFG6810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_primitiveQuarticChamberRestLF6008810PartBCDEFG6810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6008810 A B C D E F G =
      primitiveQuarticChamberRestLF6008810PartBCDEFG1810 A B C D E F G +
        primitiveQuarticChamberRestLF6008810PartBCDEFG2810 A B C D E F G +
        primitiveQuarticChamberRestLF6008810PartBCDEFG3810 A B C D E F G +
        primitiveQuarticChamberRestLF6008810PartBCDEFG4810 A B C D E F G +
        primitiveQuarticChamberRestLF6008810PartBCDEFG5810 A B C D E F G +
        primitiveQuarticChamberRestLF6008810PartBCDEFG6810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [primitiveQuarticChamberRestLF6008810, primitiveQuarticChamberRestLF6008810PartBCDEFG1810, primitiveQuarticChamberRestLF6008810PartBCDEFG2810, primitiveQuarticChamberRestLF6008810PartBCDEFG3810, primitiveQuarticChamberRestLF6008810PartBCDEFG4810, primitiveQuarticChamberRestLF6008810PartBCDEFG5810, primitiveQuarticChamberRestLF6008810PartBCDEFG6810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
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
    (hd7 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd8 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hd9 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd10 : 4 * B.natDegree + D.natDegree < d)
    (hd11 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd12 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hd13 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd14 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hd15 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hd16 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd17 : A.natDegree + 3 * D.natDegree < d)
    (hd18 : 3 * B.natDegree + G.natDegree < d)
    (hd19 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd20 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd21 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd22 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd23 : 3 * C.natDegree + D.natDegree < d)
    (hd24 : A.natDegree + F.natDegree + G.natDegree < d)
    (hd25 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd26 : B.natDegree + 2 * F.natDegree < d)
    (hd27 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd28 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd29 : 2 * D.natDegree + F.natDegree < d)
    (hd30 : D.natDegree + 2 * E.natDegree < d) :
    (primitiveQuarticChamberRestLF6008810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF6008810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (primitiveQuarticChamberRestLF6008810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF6008810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8 hd9 hd10 hd11)) (primitiveQuarticChamberRestLF6008810PartBCDEFG3810_natDegree_lt A B C D E F G hdpos hd12 hd13 hd14 hd15 hd16 hd17)) (primitiveQuarticChamberRestLF6008810PartBCDEFG4810_natDegree_lt A B C D E F G hdpos hd18 hd19 hd20 hd21 hd22 hd23)) (primitiveQuarticChamberRestLF6008810PartBCDEFG5810_natDegree_lt A B C D E F G hdpos hd24 hd25 hd26 hd27 hd28 hd29)) (primitiveQuarticChamberRestLF6008810PartBCDEFG6810_natDegree_lt A B C D E F G hdpos hd30))

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest6008810_natDegree_lt_of_live_BCDEFG
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
    (hl7 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hl8 : A.natDegree + 2 * B.natDegree + C.natDegree + D.natDegree < d)
    (hl9 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl10 : 4 * B.natDegree + D.natDegree < d)
    (hl11 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl12 : 2 * A.natDegree + E.natDegree + F.natDegree < d)
    (hl13 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl14 : A.natDegree + B.natDegree + D.natDegree + F.natDegree < d)
    (hl15 : A.natDegree + B.natDegree + 2 * E.natDegree < d)
    (hl16 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hl17 : A.natDegree + 3 * D.natDegree < d)
    (hl18 : 3 * B.natDegree + G.natDegree < d)
    (hl19 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl20 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hl21 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hl22 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hl23 : 3 * C.natDegree + D.natDegree < d)
    (hl24 : A.natDegree + F.natDegree + G.natDegree < d)
    (hl25 : B.natDegree + E.natDegree + G.natDegree < d)
    (hl26 : B.natDegree + 2 * F.natDegree < d)
    (hl27 : C.natDegree + D.natDegree + G.natDegree < d)
    (hl28 : C.natDegree + E.natDegree + F.natDegree < d)
    (hl29 : 2 * D.natDegree + F.natDegree < d)
    (hl30 : D.natDegree + 2 * E.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 5 * A.natDegree + E.natDegree < d ∧ 4 * A.natDegree + B.natDegree + D.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * A.natDegree + C.natDegree + E.natDegree < d ∧ 3 * A.natDegree + 2 * D.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * A.natDegree + D.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 2 * E.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree + E.natDegree < d ∧ A.natDegree + 2 * C.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + 2 * D.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 2 * B.natDegree + C.natDegree + E.natDegree < d ∧ 2 * B.natDegree + 2 * D.natDegree < d ∧ B.natDegree + 2 * C.natDegree + D.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + E.natDegree + G.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d ∧ B.natDegree + D.natDegree + G.natDegree < d ∧ B.natDegree + E.natDegree + F.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ C.natDegree + D.natDegree + F.natDegree < d ∧ C.natDegree + 2 * E.natDegree < d ∧ 2 * D.natDegree + E.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + E.natDegree < d ∧ 3 * A.natDegree + B.natDegree + D.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + E.natDegree < d ∧ 2 * A.natDegree + 2 * D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * E.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ B.natDegree + D.natDegree + E.natDegree < d ∧ 2 * C.natDegree + E.natDegree < d ∧ C.natDegree + 2 * D.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + C.natDegree + E.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest6008810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF6008810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14 hl15 hl16 hl17 hl18 hl19 hl20 hl21 hl22 hl23 hl24 hl25 hl26 hl27 hl28 hl29 hl30
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
  simp only [primitiveQuarticChamberRest6008810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF6004810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_kappaQuarticChamberRestLF6004810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF6004810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF6004810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6004810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 3 * B.natDegree < d)
    (hd1 : 2 * B.natDegree + D.natDegree < d)
    (hd2 : C.natDegree + F.natDegree < d) :
    (kappaQuarticChamberRestLF6004810 A B C D E F G).natDegree < d := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  rw [refl810PolyOf_ChamberUnownedSystemRests10_kappaQuarticChamberRestLF6004810]
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
theorem kappaQuarticChamberRest6004810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 3 * B.natDegree < d)
    (hl1 : 2 * B.natDegree + D.natDegree < d)
    (hl2 : C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + E.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (D.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6004810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2
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
  simp only [kappaQuarticChamberRest6004810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `nuQuarticChamberRestLF6004810` on the live set `BCDEFG` (6 monomials). -/
def nuQuarticChamberRestLF6004810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 4096 : k)) • (A ^ 2 * B ^ 3)
  + (45 / 1024 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (5 / 128 : k) • (A * C * F)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6004810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6004810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6004810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 4096) : k), (45 / 1024 : k), (35 / 512 : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k)
      ]
      [
      [2, 3, 0, 0, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6004810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6004810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + E.natDegree < d) :
    (nuQuarticChamberRestLF6004810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6004810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `nuQuarticChamberRestLF6004810` on the live set `BCDEFG` (2 monomials). -/
def nuQuarticChamberRestLF6004810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B * D ^ 2)
  + (5 / 16 : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6004810PartBCDEFG2810` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6004810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6004810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (5 / 16 : k)
      ]
      [
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6004810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6004810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * D.natDegree < d)
    (hd1 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6004810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_nuQuarticChamberRestLF6004810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6004810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6004810 A B C D E F G =
      nuQuarticChamberRestLF6004810PartBCDEFG1810 A B C D E F G +
        nuQuarticChamberRestLF6004810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [nuQuarticChamberRestLF6004810, nuQuarticChamberRestLF6004810PartBCDEFG1810, nuQuarticChamberRestLF6004810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6004810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hd2 : 3 * B.natDegree + C.natDegree < d)
    (hd3 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd4 : 2 * B.natDegree + F.natDegree < d)
    (hd5 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd6 : B.natDegree + 2 * D.natDegree < d)
    (hd7 : E.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6004810 A B C D E F G).natDegree < d := by
  rw [nuQuarticChamberRestLF6004810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (nuQuarticChamberRestLF6004810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (nuQuarticChamberRestLF6004810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7))

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRest6004810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : 2 * A.natDegree + 3 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + D.natDegree < d)
    (hl2 : 3 * B.natDegree + C.natDegree < d)
    (hl3 : A.natDegree + C.natDegree + F.natDegree < d)
    (hl4 : 2 * B.natDegree + F.natDegree < d)
    (hl5 : B.natDegree + C.natDegree + E.natDegree < d)
    (hl6 : B.natDegree + 2 * D.natDegree < d)
    (hl7 : E.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + E.natDegree < d ∧ 2 * A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 2 * D.natDegree < d ∧ 2 * B.natDegree + E.natDegree < d ∧ B.natDegree + C.natDegree + D.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d ∧ D.natDegree + F.natDegree < d ∧ 2 * E.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + E.natDegree < d ∧ A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d ∧ E.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d ∧ D.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest6004810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF6004810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
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
  simp only [nuQuarticChamberRest6004810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `xiQuarticChamberRestLF6002810` on the live set `BCDEFG` (6 monomials). -/
def xiQuarticChamberRestLF6002810PartBCDEFG1810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 2048 : k)) • (A * B ^ 4)
  + (15 / 512 : k) • (A * B ^ 2 * E)
  + (55 / 1024 : k) • (B ^ 3 * D)
  + (45 / 512 : k) • (B ^ 2 * C ^ 2)
  - (5 / 64 : k) • (A * D * F)
  - (5 / 64 : k) • (B ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6002810PartBCDEFG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6002810PartBCDEFG1810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6002810PartBCDEFG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 2048) : k), (15 / 512 : k), (55 / 1024 : k),
      (45 / 512 : k), (-(5 / 64) : k), (-(5 / 64) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 1, 0], [0, 2, 0, 0, 0, 0, 1]
      ] := by
  simp only [xiQuarticChamberRestLF6002810PartBCDEFG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6002810PartBCDEFG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d) :
    (xiQuarticChamberRestLF6002810PartBCDEFG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6002810PartBCDEFG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `xiQuarticChamberRestLF6002810` on the live set `BCDEFG` (3 monomials). -/
def xiQuarticChamberRestLF6002810PartBCDEFG2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(25 / 128 : k)) • (B * C * F)
  - (25 / 128 : k) • (B * D * E)
  + (5 / 32 : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `xiQuarticChamberRestLF6002810PartBCDEFG2810` (3 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6002810PartBCDEFG2810
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6002810PartBCDEFG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(25 / 128) : k), (-(25 / 128) : k), (5 / 32 : k)
      ]
      [
      [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [xiQuarticChamberRestLF6002810PartBCDEFG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6002810PartBCDEFG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd1 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd2 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF6002810PartBCDEFG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests10_xiQuarticChamberRestLF6002810PartBCDEFG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6002810_split_of_live_BCDEFG
    (A B C D E F G : k[X]) :
    xiQuarticChamberRestLF6002810 A B C D E F G =
      xiQuarticChamberRestLF6002810PartBCDEFG1810 A B C D E F G +
        xiQuarticChamberRestLF6002810PartBCDEFG2810 A B C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have hpow6 : (0 : k[X]) ^ 6 = 0 := zero_pow (by decide)
  have hpow7 : (0 : k[X]) ^ 7 = 0 := zero_pow (by decide)
  have hpow8 : (0 : k[X]) ^ 8 = 0 := zero_pow (by decide)
  simp only [xiQuarticChamberRestLF6002810, xiQuarticChamberRestLF6002810PartBCDEFG1810, xiQuarticChamberRestLF6002810PartBCDEFG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRestLF6002810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : A.natDegree + 4 * B.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd2 : 3 * B.natDegree + D.natDegree < d)
    (hd3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + G.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd8 : 2 * F.natDegree < d) :
    (xiQuarticChamberRestLF6002810 A B C D E F G).natDegree < d := by
  rw [xiQuarticChamberRestLF6002810_split_of_live_BCDEFG A B C D E F G]
  exact (natDegree_add_lt810 (xiQuarticChamberRestLF6002810PartBCDEFG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (xiQuarticChamberRestLF6002810PartBCDEFG2810_natDegree_lt A B C D E F G hdpos hd6 hd7 hd8))

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberRest6002810_natDegree_lt_of_live_BCDEFG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hl0 : A.natDegree + 4 * B.natDegree < d)
    (hl1 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hl2 : 3 * B.natDegree + D.natDegree < d)
    (hl3 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hl4 : A.natDegree + D.natDegree + F.natDegree < d)
    (hl5 : 2 * B.natDegree + G.natDegree < d)
    (hl6 : B.natDegree + C.natDegree + F.natDegree < d)
    (hl7 : B.natDegree + D.natDegree + E.natDegree < d)
    (hl8 : 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + D.natDegree < d ∧ 3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + E.natDegree < d ∧ 2 * A.natDegree + C.natDegree + D.natDegree < d ∧ A.natDegree + 2 * B.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + D.natDegree + E.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + C.natDegree + E.natDegree < d ∧ B.natDegree + 2 * D.natDegree < d ∧ 2 * C.natDegree + D.natDegree < d ∧ D.natDegree + G.natDegree < d ∧ E.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + E.natDegree < d ∧ A.natDegree + C.natDegree + D.natDegree < d ∧ 2 * B.natDegree + D.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d ∧ D.natDegree + E.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + D.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d ∧ C.natDegree + E.natDegree < d ∧ 2 * D.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d ∧ B.natDegree + E.natDegree < d ∧ C.natDegree + D.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ B.natDegree + D.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + D.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * B.natDegree < d ∧ E.natDegree < d))
    (hbtheta : theta = 0 ∨ (D.natDegree < d)) :
    (xiQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    xiQuarticChamberRestLF6002810_natDegree_lt_of_live_BCDEFG
      A B C D E F G hdpos hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8
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
  simp only [xiQuarticChamberRest6002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7


end QuarticChamberUnownedSystemRests10810

end Max11DegreeRoutes
