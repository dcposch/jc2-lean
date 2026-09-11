import Grok810ScaleZeroQuarticChamberColumnsScratch
import Grok810ScaleZeroQuarticChamberColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemColumns1Scratch

/-! # UnownedSystem chamber rests, part 1/11

40 of the 180 load-free and 180 full (packet,
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

section QuarticChamberUnownedSystemRests1810

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF6000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
      A B C D E F G hdpos hCz hDz hEz hFz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BG l A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BG beta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
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
    simp only [kappaQuarticColumnGamma810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BG delta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BG zeta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BG eta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BG theta A B C D E F G hdpos hCz hDz hEz hFz g0
  simp only [kappaQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (nuQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  simp only [nuQuarticChamberRestLF6000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRest6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * B.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d)) :
    (nuQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
      A B C D E F G hdpos hCz hDz hEz hFz
  have hc0 : (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnL810_zero]
      simpa using hdpos
    · exact nuQuarticColumnL810_natDegree_lt_of_live_BG l A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc1 : (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnBeta810_natDegree_lt_of_live_BG beta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc2 : (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [nuQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact nuQuarticColumnGamma810_natDegree_lt_of_live_BG gamma A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc3 : (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnDelta810_natDegree_lt_of_live_BG delta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc4 : (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [nuQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnZeta810_natDegree_lt_of_live_BG zeta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc6 : (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [nuQuarticColumnEta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEta810_natDegree_lt_of_live_BG eta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc7 : (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [nuQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnTheta810_natDegree_lt_of_live_BG theta A B C D E F G hdpos hCz hDz hEz hFz g0
  simp only [nuQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6000810` (22 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_omicronQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 16384) : k), (15 / 16384 : k), (-(35 / 2048) : k),
      (-(21 / 4096) : k), (-(5 / 2048) : k), (-(5 / 2048) : k),
      (25 / 1024 : k), (15 / 512 : k), (35 / 1024 : k),
      (15 / 1024 : k), (5 / 128 : k), (135 / 1024 : k),
      (45 / 1024 : k), (-(5 / 128) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(5 / 32) : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (-(25 / 128) : k), (-(5 / 128) : k),
      (5 / 16 : k)
      ]
      [
      [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0],
      [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0],
      [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1]
      ] := by
  simp only [omicronQuarticChamberRestLF6000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 5 * B.natDegree < d) :
    (omicronQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_omicronQuarticChamberRestLF6000810]
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
theorem omicronQuarticChamberRest6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 5 * B.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 4 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 3 * B.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (3 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d)) :
    (omicronQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
      A B C D E F G hdpos hCz hDz hEz hFz hl0
  have hc0 : (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [omicronQuarticColumnL1810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnL1810_natDegree_lt_of_live_BG l A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2 g3 g4
  have hc1 : (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
    simp only [omicronQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnBeta810_natDegree_lt_of_live_BG beta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc3 : (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [omicronQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnGamma810_natDegree_lt_of_live_BG gamma A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc4 : (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [omicronQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnDelta810_natDegree_lt_of_live_BG delta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc5 : (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [omicronQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BG epsilon A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc6 : (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnZeta810_natDegree_lt_of_live_BG zeta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc7 : (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [omicronQuarticColumnEta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEta810_natDegree_lt_of_live_BG eta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc8 : (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [omicronQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnTheta810_natDegree_lt_of_live_BG theta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  simp only [omicronQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF6000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (3 * A.natDegree + 3 * B.natDegree < d ∧ 5 * B.natDegree < d))
    (hbbeta : beta = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (4 * B.natDegree < d))
    (hbdelta : delta = 0 ∨ (A.natDegree + 3 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d)) :
    (piQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
      A B C D E F G hdpos hCz hDz hEz hFz
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BG l A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
    rcases hbbeta with rfl | g0
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BG beta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BG gamma A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | g0
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BG delta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    rcases hbzeta with rfl | g0
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BG zeta A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BG eta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6000810` (35 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 16384) : k), (15 / 16384 : k), (15 / 8192 : k),
      (65 / 8192 : k), (-(5 / 2048) : k), (-(5 / 2048) : k),
      (-(5 / 2048) : k), (15 / 1024 : k), (-(25 / 2048) : k),
      (15 / 2048 : k), (-(25 / 512) : k), (-(135 / 1024) : k),
      (-(15 / 1024) : k), (-(125 / 2048) : k), (-(265 / 2048) : k),
      (-(5 / 256) : k), (-(5 / 256) : k), (5 / 128 : k),
      (5 / 32 : k), (5 / 64 : k), (15 / 128 : k),
      (5 / 128 : k), (15 / 256 : k), (85 / 256 : k),
      (85 / 256 : k), (45 / 128 : k), (45 / 128 : k),
      (15 / 128 : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(5 / 16) : k), (-(5 / 16) : k), (-(5 / 8) : k),
      (-(5 / 16) : k), (-(5 / 16) : k)
      ]
      [
      [3, 2, 0, 1, 0, 0, 0], [3, 1, 2, 0, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0],
      [3, 0, 1, 0, 0, 1, 0], [3, 0, 0, 1, 1, 0, 0], [2, 2, 0, 0, 0, 1, 0], [2, 1, 1, 0, 1, 0, 0],
      [2, 1, 0, 2, 0, 0, 0], [2, 0, 2, 1, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 2, 1, 1, 0, 0, 0],
      [1, 1, 3, 0, 0, 0, 0], [0, 4, 0, 1, 0, 0, 0], [0, 3, 2, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 1],
      [2, 0, 0, 0, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1], [1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 0, 2, 0, 0],
      [1, 0, 1, 1, 1, 0, 0], [1, 0, 0, 3, 0, 0, 0], [0, 3, 0, 0, 0, 0, 1], [0, 2, 1, 0, 0, 1, 0],
      [0, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0], [0, 0, 3, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 2, 0], [0, 0, 1, 1, 0, 0, 1],
      [0, 0, 1, 0, 1, 1, 0], [0, 0, 0, 2, 0, 1, 0], [0, 0, 0, 1, 2, 0, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 5 * B.natDegree < d)
    (hd1 : 3 * B.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6000810]
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
theorem primitiveQuarticChamberRest6000810_natDegree_lt_of_live_BG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hCz : C = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 5 * B.natDegree < d)
    (hl1 : 3 * B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + 3 * B.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 4 * B.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + 3 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ 3 * B.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF6000810_natDegree_lt_of_live_BG
      A B C D E F G hdpos hCz hDz hEz hFz hl0 hl1
  have hc0 : (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [primitiveQuarticColumnL1810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL1810_natDegree_lt_of_live_BG l A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2 g3
  have hc1 : (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [primitiveQuarticColumnL2810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL2810_natDegree_lt_of_live_BG l A B C D E F G hdpos hCz hDz hEz hFz g4 g5
  have hc2 : (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [primitiveQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnBeta810_natDegree_lt_of_live_BG beta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc3 : (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [primitiveQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnGamma810_natDegree_lt_of_live_BG gamma A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc4 : (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [primitiveQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnDelta810_natDegree_lt_of_live_BG delta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  have hc5 : (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [primitiveQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BG epsilon A B C D E F G hdpos hCz hDz hEz hFz g0
  have hc6 : (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [primitiveQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnZeta810_natDegree_lt_of_live_BG zeta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc7 : (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [primitiveQuarticColumnEta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEta810_natDegree_lt_of_live_BG eta A B C D E F G hdpos hCz hDz hEz hFz g0 g1
  have hc8 : (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [primitiveQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnTheta810_natDegree_lt_of_live_BG theta A B C D E F G hdpos hCz hDz hEz hFz g0 g1 g2
  simp only [primitiveQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6000810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (muQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  simp only [muQuarticChamberRestLF6000810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRest6000810_natDegree_lt_of_live_CG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbgamma : gamma = 0 ∨ (2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d)) :
    (muQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF6000810_natDegree_lt_of_live_CG
      A B C D E F G hdpos hBz hDz hEz hFz
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnL810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnBeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_CG gamma A B C D E F G hdpos hBz hDz hEz hFz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnDelta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnZeta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_CG eta A B C D E F G hdpos hBz hDz hEz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
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
    simp only [muQuarticColumnTheta810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  simp only [muQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6001810_natDegree_lt_of_live_CG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (piQuarticChamberRestLF6001810 A B C D E F G).natDegree < d := by
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
  simp only [piQuarticChamberRestLF6001810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRest6001810_natDegree_lt_of_live_CG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hBz : B = 0)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbgamma : gamma = 0 ∨ (3 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * C.natDegree < d ∧ G.natDegree < d)) :
    (piQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF6001810_natDegree_lt_of_live_CG
      A B C D E F G hdpos hBz hDz hEz hFz
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
  simp only [piQuarticChamberRest6001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    (kappaQuarticChamberRestLF6001810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF6001810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0
  simp only [kappaQuarticChamberRest6001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF6001810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_muQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF6001810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (5 / 16 : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF6001810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF6001810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_muQuarticChamberRestLF6001810]
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
theorem muQuarticChamberRest6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCF epsilon A B C D E F G hdpos hDz hEz hGz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0
  simp only [muQuarticChamberRest6001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6001810` (10 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_nuQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6001810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (35 / 512 : k), (-(5 / 128) : k),
      (-(5 / 128) : k), (-(15 / 128) : k), (-(15 / 64) : k),
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k)
      ]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6001810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 3 * B.natDegree + C.natDegree < d)
    (hd1 : 2 * B.natDegree + F.natDegree < d) :
    (nuQuarticChamberRestLF6001810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_nuQuarticChamberRestLF6001810]
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
theorem nuQuarticChamberRest6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 3 * B.natDegree + C.natDegree < d)
    (hl1 : 2 * B.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ A.natDegree + B.natDegree + F.natDegree < d ∧ 3 * C.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0 hl1
  have hc0 : (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [nuQuarticColumnL810_zero]
      simpa using hdpos
    · exact nuQuarticColumnL810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [nuQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4
  have hc2 : (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [nuQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact nuQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc3 : (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [nuQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc4 : (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCF epsilon A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc5 : (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc6 : (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [nuQuarticColumnEta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0
  have hc7 : (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0 g1
  simp only [nuQuarticChamberRest6001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `omicronQuarticChamberRestLF6001810` (21 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_omicronQuarticChamberRestLF6001810
    (A B C D E F G : k[X]) :
    omicronQuarticChamberRestLF6001810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 16384) : k), (-(35 / 2048) : k), (-(21 / 4096) : k),
      (-(5 / 2048) : k), (-(5 / 2048) : k), (25 / 1024 : k),
      (15 / 512 : k), (35 / 1024 : k), (15 / 1024 : k),
      (5 / 128 : k), (135 / 1024 : k), (45 / 1024 : k),
      (-(5 / 128) : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(5 / 32) : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(25 / 128) : k), (-(5 / 128) : k), (5 / 16 : k)
      ]
      [
      [2, 2, 0, 1, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [2, 1, 0, 0, 0, 0, 1],
      [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0],
      [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
      [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0],
      [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 1]
      ] := by
  simp only [omicronQuarticChamberRestLF6001810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : 5 * B.natDegree < d)
    (hd2 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd3 : B.natDegree + 3 * C.natDegree < d)
    (hd4 : 2 * C.natDegree + F.natDegree < d) :
    (omicronQuarticChamberRestLF6001810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_omicronQuarticChamberRestLF6001810]
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
theorem omicronQuarticChamberRest6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl1 : 5 * B.natDegree < d)
    (hl2 : A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl3 : B.natDegree + 3 * C.natDegree < d)
    (hl4 : 2 * C.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + F.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d ∧ F.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d)) :
    (omicronQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0 hl1 hl2 hl3 hl4
  have hc0 : (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [omicronQuarticColumnL1810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnL1810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [omicronQuarticColumnL2810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnL2810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g10
  have hc2 : (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [omicronQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6
  have hc3 : (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [omicronQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4
  have hc4 : (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [omicronQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5
  have hc5 : (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BCF epsilon A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc6 : (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [omicronQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc7 : (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnEta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc8 : (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  simp only [omicronQuarticChamberRest6001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6002810` (16 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_piQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6002810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(35 / 256) : k), (5 / 64 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (5 / 4 : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0],
      [0, 1, 2, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2]
      ] := by
  simp only [piQuarticChamberRestLF6002810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6002810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 4 * B.natDegree + C.natDegree < d)
    (hd1 : 3 * B.natDegree + F.natDegree < d) :
    (piQuarticChamberRestLF6002810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_piQuarticChamberRestLF6002810]
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
theorem piQuarticChamberRest6002810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 4 * B.natDegree + C.natDegree < d)
    (hl1 : 3 * B.natDegree + F.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 4 * A.natDegree + F.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ 2 * A.natDegree + C.natDegree + F.natDegree < d ∧ A.natDegree + 2 * B.natDegree + F.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ 2 * C.natDegree + F.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d ∧ F.natDegree < d)) :
    (piQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF6002810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0 hl1
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
    · rw [piQuarticColumnL2810_zero]
      simpa using hdpos
    · exact piQuarticColumnL2810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g9
  have hc2 : (piQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCF epsilon A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0 g1 g2
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0 g1
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0 g1
  simp only [piQuarticChamberRest6002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticChamberRestLF6001810` on the live set `BCF` (6 monomials). -/
def primitiveQuarticChamberRestLF6001810PartBCF1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (85 / 256 : k) • (B ^ 2 * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6001810PartBCF1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6001810PartBCF1810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6001810PartBCF1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 8192 : k), (65 / 8192 : k), (-(5 / 2048) : k),
      (-(15 / 1024) : k), (-(265 / 2048) : k), (85 / 256 : k)
      ]
      [
      [2, 3, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0], [1, 1, 3, 0, 0, 0, 0],
      [0, 3, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 1, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6001810PartBCF1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6001810PartBCF1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 5 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + F.natDegree < d) :
    (primitiveQuarticChamberRestLF6001810PartBCF1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6001810PartBCF1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticChamberRestLF6001810` on the live set `BCF` (1 monomials). -/
def primitiveQuarticChamberRestLF6001810PartBCF2810
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (B * F ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6001810PartBCF2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6001810PartBCF2810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6001810PartBCF2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k)
      ]
      [
      [0, 1, 0, 0, 0, 2, 0]
      ] := by
  simp only [primitiveQuarticChamberRestLF6001810PartBCF2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6001810PartBCF2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : B.natDegree + 2 * F.natDegree < d) :
    (primitiveQuarticChamberRestLF6001810PartBCF2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6001810PartBCF2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6001810_split_of_live_BCF
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0) :
    primitiveQuarticChamberRestLF6001810 A B C D E F G =
      primitiveQuarticChamberRestLF6001810PartBCF1810 A B C D E F G +
        primitiveQuarticChamberRestLF6001810PartBCF2810 A B C D E F G := by
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
  simp only [primitiveQuarticChamberRestLF6001810, primitiveQuarticChamberRestLF6001810PartBCF1810, primitiveQuarticChamberRestLF6001810PartBCF2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hd0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 5 * B.natDegree < d)
    (hd2 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + 2 * F.natDegree < d) :
    (primitiveQuarticChamberRestLF6001810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF6001810_split_of_live_BCF A B C D E F G hDz hEz hGz]
  exact natDegree_add_lt810 (primitiveQuarticChamberRestLF6001810PartBCF1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF6001810PartBCF2810_natDegree_lt A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest6001810_natDegree_lt_of_live_BCF
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hGz : G = 0)
    (hl0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl1 : A.natDegree + 5 * B.natDegree < d)
    (hl2 : 2 * A.natDegree + 2 * B.natDegree + F.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl5 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hl6 : B.natDegree + 2 * F.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + B.natDegree + F.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree + F.natDegree < d ∧ 3 * B.natDegree + F.natDegree < d ∧ 4 * C.natDegree < d ∧ A.natDegree + 2 * F.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + C.natDegree + F.natDegree < d ∧ 2 * F.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ 3 * A.natDegree + F.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d ∧ A.natDegree + C.natDegree + F.natDegree < d ∧ 2 * B.natDegree + F.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + F.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ C.natDegree + F.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ B.natDegree + F.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d ∧ A.natDegree + F.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d)) :
    (primitiveQuarticChamberRest6001810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF6001810_natDegree_lt_of_live_BCF
      A B C D E F G hdpos hDz hEz hGz hl0 hl1 hl2 hl3 hl4 hl5 hl6
  have hc0 : (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
    · rw [primitiveQuarticColumnL1810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL1810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have hc1 : (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
    · rw [primitiveQuarticColumnL2810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL2810_natDegree_lt_of_live_BCF l A B C D E F G hdpos hDz hEz hGz g10 g11 g12 g13
  have hc2 : (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩
    · rw [primitiveQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCF beta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hc3 : (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCF gamma A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6
  have hc4 : (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCF delta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [primitiveQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCF epsilon A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4
  have hc6 : (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [primitiveQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnZeta810_natDegree_lt_of_live_BCF zeta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3 g4
  have hc7 : (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [primitiveQuarticColumnEta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEta810_natDegree_lt_of_live_BCF eta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  have hc8 : (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [primitiveQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnTheta810_natDegree_lt_of_live_BCF theta A B C D E F G hdpos hDz hEz hGz g0 g1 g2 g3
  simp only [primitiveQuarticChamberRest6001810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `kappaQuarticChamberRestLF6000810` (4 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_kappaQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) :
    kappaQuarticChamberRestLF6000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(15 / 128) : k), (5 / 16 : k),
      (5 / 16 : k)
      ]
      [
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]
      ] := by
  simp only [kappaQuarticChamberRestLF6000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : B.natDegree + 2 * C.natDegree < d) :
    (kappaQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_kappaQuarticChamberRestLF6000810]
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
theorem kappaQuarticChamberRest6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : B.natDegree + 2 * C.natDegree < d)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0
  simp only [kappaQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `nuQuarticChamberRestLF6000810` (11 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_nuQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) :
    nuQuarticChamberRestLF6000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (15 / 1024 : k), (35 / 512 : k),
      (-(5 / 128) : k), (-(5 / 128) : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k)
      ]
      [
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [nuQuarticChamberRestLF6000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : 3 * B.natDegree + C.natDegree < d) :
    (nuQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_nuQuarticChamberRestLF6000810]
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
theorem nuQuarticChamberRest6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hl1 : 3 * B.natDegree + C.natDegree < d)
    (hbl : l = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 2 * A.natDegree + G.natDegree < d ∧ 3 * C.natDegree < d ∧ C.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbdelta : delta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbzeta : zeta = 0 ∨ (3 * A.natDegree < d ∧ 2 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbtheta : theta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d)) :
    (nuQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    nuQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0 hl1
  have hc0 : (nuQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩
    · rw [nuQuarticColumnL810_zero]
      simpa using hdpos
    · exact nuQuarticColumnL810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6 g7
  have hc1 : (nuQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [nuQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3
  have hc2 : (nuQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact nuQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc3 : (nuQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [nuQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc4 : (nuQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [nuQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEpsilon810_natDegree_lt_of_live_BCG epsilon A B C D E F G hdpos hDz hEz hFz g0
  have hc5 : (nuQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc6 : (nuQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [nuQuarticColumnEta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0
  have hc7 : (nuQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1⟩
    · rw [nuQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact nuQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0 g1
  simp only [nuQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : 5 * B.natDegree < d)
    (hd3 : B.natDegree + 3 * C.natDegree < d)
    (hd4 : B.natDegree + C.natDegree + G.natDegree < d) :
    (omicronQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_omicronQuarticChamberRestLF6000810]
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
theorem omicronQuarticChamberRest6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hl1 : A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl2 : 5 * B.natDegree < d)
    (hl3 : B.natDegree + 3 * C.natDegree < d)
    (hl4 : B.natDegree + C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 3 * A.natDegree + G.natDegree < d ∧ A.natDegree + 3 * C.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + C.natDegree + G.natDegree < d ∧ 2 * B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbeta : eta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbtheta : theta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d)) :
    (omicronQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    omicronQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0 hl1 hl2 hl3 hl4
  have hc0 : (omicronQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩
    · rw [omicronQuarticColumnL1810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnL1810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (omicronQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
    simp only [omicronQuarticColumnL2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc2 : (omicronQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [omicronQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6
  have hc3 : (omicronQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc4 : (omicronQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [omicronQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc5 : (omicronQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1⟩
    · rw [omicronQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEpsilon810_natDegree_lt_of_live_BCG epsilon A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc6 : (omicronQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [omicronQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc7 : (omicronQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1⟩
    · rw [omicronQuarticColumnEta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc8 : (omicronQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2⟩
    · rw [omicronQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact omicronQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  simp only [omicronQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `piQuarticChamberRestLF6000810` (18 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_piQuarticChamberRestLF6000810
    (A B C D E F G : k[X]) :
    piQuarticChamberRestLF6000810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(15 / 128) : k), (-(45 / 512) : k), (-(35 / 256) : k),
      (5 / 32 : k), (5 / 16 : k), (5 / 32 : k),
      (25 / 128 : k), (45 / 64 : k), (45 / 128 : k),
      (45 / 64 : k), (15 / 256 : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (-(15 / 16) : k), (-(5 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0],
      [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 0, 2, 0],
      [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0]
      ] := by
  simp only [piQuarticChamberRestLF6000810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem piQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd1 : 4 * B.natDegree + C.natDegree < d)
    (hd2 : 4 * C.natDegree < d)
    (hd3 : 2 * C.natDegree + G.natDegree < d) :
    (piQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_piQuarticChamberRestLF6000810]
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
theorem piQuarticChamberRest6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hl1 : 4 * B.natDegree + C.natDegree < d)
    (hl2 : 4 * C.natDegree < d)
    (hl3 : 2 * C.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 3 * B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 3 * B.natDegree + C.natDegree < d ∧ 5 * B.natDegree < d ∧ B.natDegree + 3 * C.natDegree < d ∧ B.natDegree + C.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree + C.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbeta : eta = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree + C.natDegree < d)) :
    (piQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    piQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0 hl1 hl2 hl3
  have hc0 : (piQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [piQuarticColumnL1810_zero]
      simpa using hdpos
    · exact piQuarticColumnL1810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6
  have hc1 : (piQuarticColumnL2810 l A B C D E F G).natDegree < d := by
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
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [piQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3
  have hc3 : (piQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact piQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc4 : (piQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact piQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc5 : (piQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [piQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact piQuarticColumnEpsilon810_natDegree_lt_of_live_BCG epsilon A B C D E F G hdpos hDz hEz hFz g0
  have hc6 : (piQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [piQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact piQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc7 : (piQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [piQuarticColumnEta810_zero]
      simpa using hdpos
    · exact piQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc8 : (piQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [piQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact piQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0
  simp only [piQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
/-- Piece 1/2 of `primitiveQuarticChamberRestLF6000810` on the live set `BCG` (6 monomials). -/
def primitiveQuarticChamberRestLF6000810PartBCG1810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  + (5 / 128 : k) • (A * B * C * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6000810PartBCG1810` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6000810PartBCG1810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6000810PartBCG1810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 16384 : k), (15 / 8192 : k), (65 / 8192 : k),
      (-(15 / 1024) : k), (-(265 / 2048) : k), (5 / 128 : k)
      ]
      [
      [3, 1, 2, 0, 0, 0, 0], [2, 3, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0], [1, 1, 3, 0, 0, 0, 0],
      [0, 3, 2, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 1]
      ] := by
  simp only [primitiveQuarticChamberRestLF6000810PartBCG1810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6000810PartBCG1810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 5 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF6000810PartBCG1810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6000810PartBCG1810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Piece 2/2 of `primitiveQuarticChamberRestLF6000810` on the live set `BCG` (1 monomials). -/
def primitiveQuarticChamberRestLF6000810PartBCG2810
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 256 : k) • (B ^ 3 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `primitiveQuarticChamberRestLF6000810PartBCG2810` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6000810PartBCG2810
    (A B C D E F G : k[X]) :
    primitiveQuarticChamberRestLF6000810PartBCG2810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 256 : k)
      ]
      [
      [0, 3, 0, 0, 0, 0, 1]
      ] := by
  simp only [primitiveQuarticChamberRestLF6000810PartBCG2810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6000810PartBCG2810_natDegree_lt
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hd0 : 3 * B.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF6000810PartBCG2810 A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberUnownedSystemRests1_primitiveQuarticChamberRestLF6000810PartBCG2810]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6000810_split_of_live_BCG
    (A B C D E F G : k[X])
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    primitiveQuarticChamberRestLF6000810 A B C D E F G =
      primitiveQuarticChamberRestLF6000810PartBCG1810 A B C D E F G +
        primitiveQuarticChamberRestLF6000810PartBCG2810 A B C D E F G := by
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
  simp only [primitiveQuarticChamberRestLF6000810, primitiveQuarticChamberRestLF6000810PartBCG1810, primitiveQuarticChamberRestLF6000810PartBCG2810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd2 : A.natDegree + 5 * B.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd6 : 3 * B.natDegree + G.natDegree < d) :
    (primitiveQuarticChamberRestLF6000810 A B C D E F G).natDegree < d := by
  rw [primitiveQuarticChamberRestLF6000810_split_of_live_BCG A B C D E F G hDz hEz hFz]
  exact natDegree_add_lt810 (primitiveQuarticChamberRestLF6000810PartBCG1810_natDegree_lt A B C D E F G hdpos hd0 hd1 hd2 hd3 hd4 hd5) (primitiveQuarticChamberRestLF6000810PartBCG2810_natDegree_lt A B C D E F G hdpos hd6)

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberRest6000810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hl1 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hl2 : A.natDegree + 5 * B.natDegree < d)
    (hl3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hl4 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hl5 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hl6 : 3 * B.natDegree + G.natDegree < d)
    (hbl : l = 0 ∨ (8 * A.natDegree < d ∧ 6 * A.natDegree + C.natDegree < d ∧ 5 * A.natDegree + 2 * B.natDegree < d ∧ 4 * A.natDegree + 2 * C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 4 * B.natDegree < d ∧ 4 * A.natDegree + G.natDegree < d ∧ 2 * A.natDegree + 3 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d ∧ 4 * B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + C.natDegree + G.natDegree < d ∧ A.natDegree + 2 * B.natDegree + G.natDegree < d ∧ 4 * C.natDegree < d ∧ 2 * C.natDegree + G.natDegree < d ∧ 2 * G.natDegree < d))
    (hbbeta : beta = 0 ∨ (7 * A.natDegree < d ∧ 5 * A.natDegree + C.natDegree < d ∧ 4 * A.natDegree + 2 * B.natDegree < d ∧ 3 * A.natDegree + 2 * C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + 4 * B.natDegree < d ∧ 2 * B.natDegree + 2 * C.natDegree < d))
    (hbgamma : gamma = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 3 * B.natDegree < d ∧ A.natDegree + B.natDegree + 2 * C.natDegree < d ∧ 3 * B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (6 * A.natDegree < d ∧ 4 * A.natDegree + C.natDegree < d ∧ 3 * A.natDegree + 2 * B.natDegree < d ∧ 2 * A.natDegree + 2 * C.natDegree < d ∧ A.natDegree + 2 * B.natDegree + C.natDegree < d ∧ 4 * B.natDegree < d ∧ 3 * C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d))
    (hbzeta : zeta = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d))
    (hbeta : eta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbtheta : theta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d)) :
    (primitiveQuarticChamberRest6000810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    primitiveQuarticChamberRestLF6000810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0 hl1 hl2 hl3 hl4 hl5 hl6
  have hc0 : (primitiveQuarticColumnL1810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [primitiveQuarticColumnL1810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL1810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  have hc1 : (primitiveQuarticColumnL2810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    · rw [primitiveQuarticColumnL2810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnL2810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g11 g12 g13 g14
  have hc2 : (primitiveQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6
  have hc3 : (primitiveQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2, g3⟩
    · rw [primitiveQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3
  have hc4 : (primitiveQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2, g3, g4, g5, g6⟩
    · rw [primitiveQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5 g6
  have hc5 : (primitiveQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | ⟨g0, g1, g2⟩
    · rw [primitiveQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEpsilon810_natDegree_lt_of_live_BCG epsilon A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc6 : (primitiveQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1, g2, g3⟩
    · rw [primitiveQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3
  have hc7 : (primitiveQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | ⟨g0, g1, g2⟩
    · rw [primitiveQuarticColumnEta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc8 : (primitiveQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [primitiveQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact primitiveQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  simp only [primitiveQuarticChamberRest6000810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7) hc8

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRestLF6002810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0) :
    (kappaQuarticChamberRestLF6002810 A B C D E F G).natDegree < d := by
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
  simp only [kappaQuarticChamberRestLF6002810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
  omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberRest6002810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hbl : l = 0 ∨ (5 * A.natDegree < d ∧ 3 * A.natDegree + C.natDegree < d ∧ 2 * A.natDegree + 2 * B.natDegree < d ∧ A.natDegree + 2 * C.natDegree < d ∧ 2 * B.natDegree + C.natDegree < d ∧ A.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (4 * A.natDegree < d ∧ 2 * A.natDegree + C.natDegree < d ∧ A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbgamma : gamma = 0 ∨ (B.natDegree + C.natDegree < d))
    (hbdelta : delta = 0 ∨ (3 * A.natDegree < d ∧ A.natDegree + C.natDegree < d ∧ 2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (2 * A.natDegree < d ∧ C.natDegree < d))
    (hbeta : eta = 0 ∨ (B.natDegree < d))
    (hbtheta : theta = 0 ∨ (A.natDegree < d)) :
    (kappaQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    kappaQuarticChamberRestLF6002810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz
  have hc0 : (kappaQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4, g5⟩
    · rw [kappaQuarticColumnL810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnL810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4 g5
  have hc1 : (kappaQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [kappaQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc2 : (kappaQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | g0
    · rw [kappaQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0
  have hc3 : (kappaQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1, g2⟩
    · rw [kappaQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc4 : (kappaQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
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
    simp only [kappaQuarticColumnEpsilon810, hpow2, hpow3, hpow4, hpow5, hpow6, hpow7, hpow8, zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, natDegree_zero]
    omega
  have hc5 : (kappaQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | ⟨g0, g1⟩
    · rw [kappaQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc6 : (kappaQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [kappaQuarticColumnEta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0
  have hc7 : (kappaQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [kappaQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact kappaQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0
  simp only [kappaQuarticChamberRest6002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `muQuarticChamberRestLF6002810` (7 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberUnownedSystemRests1_muQuarticChamberRestLF6002810
    (A B C D E F G : k[X]) :
    muQuarticChamberRestLF6002810 A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 2048 : k), (-(5 / 64) : k), (-(5 / 128) : k),
      (-(15 / 128) : k), (-(15 / 64) : k), (5 / 16 : k),
      (5 / 32 : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0],
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0]
      ] := by
  simp only [muQuarticChamberRestLF6002810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem muQuarticChamberRestLF6002810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hd0 : 4 * B.natDegree < d) :
    (muQuarticChamberRestLF6002810 A B C D E F G).natDegree < d := by
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
  rw [refl810PolyOf_ChamberUnownedSystemRests1_muQuarticChamberRestLF6002810]
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
theorem muQuarticChamberRest6002810_natDegree_lt_of_live_BCG
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hdpos : 0 < d)
    (hDz : D = 0)
    (hEz : E = 0)
    (hFz : F = 0)
    (hl0 : 4 * B.natDegree < d)
    (hbl : l = 0 ∨ (4 * A.natDegree + B.natDegree < d ∧ 2 * A.natDegree + B.natDegree + C.natDegree < d ∧ A.natDegree + 3 * B.natDegree < d ∧ B.natDegree + 2 * C.natDegree < d ∧ B.natDegree + G.natDegree < d))
    (hbbeta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < d ∧ A.natDegree + B.natDegree + C.natDegree < d ∧ 3 * B.natDegree < d))
    (hbgamma : gamma = 0 ∨ (A.natDegree + 2 * B.natDegree < d ∧ 2 * C.natDegree < d ∧ G.natDegree < d))
    (hbdelta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < d ∧ B.natDegree + C.natDegree < d))
    (hbepsilon : epsilon = 0 ∨ (2 * B.natDegree < d))
    (hbzeta : zeta = 0 ∨ (A.natDegree + B.natDegree < d))
    (hbeta : eta = 0 ∨ (C.natDegree < d))
    (hbtheta : theta = 0 ∨ (B.natDegree < d)) :
    (muQuarticChamberRest6002810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  have hr0 :=
    muQuarticChamberRestLF6002810_natDegree_lt_of_live_BCG
      A B C D E F G hdpos hDz hEz hFz hl0
  have hc0 : (muQuarticColumnL810 l A B C D E F G).natDegree < d := by
    rcases hbl with rfl | ⟨g0, g1, g2, g3, g4⟩
    · rw [muQuarticColumnL810_zero]
      simpa using hdpos
    · exact muQuarticColumnL810_natDegree_lt_of_live_BCG l A B C D E F G hdpos hDz hEz hFz g0 g1 g2 g3 g4
  have hc1 : (muQuarticColumnBeta810 beta A B C D E F G).natDegree < d := by
    rcases hbbeta with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnBeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnBeta810_natDegree_lt_of_live_BCG beta A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc2 : (muQuarticColumnGamma810 gamma A B C D E F G).natDegree < d := by
    rcases hbgamma with rfl | ⟨g0, g1, g2⟩
    · rw [muQuarticColumnGamma810_zero]
      simpa using hdpos
    · exact muQuarticColumnGamma810_natDegree_lt_of_live_BCG gamma A B C D E F G hdpos hDz hEz hFz g0 g1 g2
  have hc3 : (muQuarticColumnDelta810 delta A B C D E F G).natDegree < d := by
    rcases hbdelta with rfl | ⟨g0, g1⟩
    · rw [muQuarticColumnDelta810_zero]
      simpa using hdpos
    · exact muQuarticColumnDelta810_natDegree_lt_of_live_BCG delta A B C D E F G hdpos hDz hEz hFz g0 g1
  have hc4 : (muQuarticColumnEpsilon810 epsilon A B C D E F G).natDegree < d := by
    rcases hbepsilon with rfl | g0
    · rw [muQuarticColumnEpsilon810_zero]
      simpa using hdpos
    · exact muQuarticColumnEpsilon810_natDegree_lt_of_live_BCG epsilon A B C D E F G hdpos hDz hEz hFz g0
  have hc5 : (muQuarticColumnZeta810 zeta A B C D E F G).natDegree < d := by
    rcases hbzeta with rfl | g0
    · rw [muQuarticColumnZeta810_zero]
      simpa using hdpos
    · exact muQuarticColumnZeta810_natDegree_lt_of_live_BCG zeta A B C D E F G hdpos hDz hEz hFz g0
  have hc6 : (muQuarticColumnEta810 eta A B C D E F G).natDegree < d := by
    rcases hbeta with rfl | g0
    · rw [muQuarticColumnEta810_zero]
      simpa using hdpos
    · exact muQuarticColumnEta810_natDegree_lt_of_live_BCG eta A B C D E F G hdpos hDz hEz hFz g0
  have hc7 : (muQuarticColumnTheta810 theta A B C D E F G).natDegree < d := by
    rcases hbtheta with rfl | g0
    · rw [muQuarticColumnTheta810_zero]
      simpa using hdpos
    · exact muQuarticColumnTheta810_natDegree_lt_of_live_BCG theta A B C D E F G hdpos hDz hEz hFz g0
  simp only [muQuarticChamberRest6002810]
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hr0 hc0) hc1) hc2) hc3) hc4) hc5) hc6) hc7


end QuarticChamberUnownedSystemRests1810

end Max11DegreeRoutes
