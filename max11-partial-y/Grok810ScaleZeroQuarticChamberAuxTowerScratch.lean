import Grok810ScaleZeroQuarticChamberFacesScratch

/-! # The odd `A`-power auxiliary tower, `(8,10)` scale zero

`N₄ = Π − A·ο`, `N₅ = ο + (1/8)A·ν + (3/128)A²·κ`,
`N₆ = Π − (2/3)A·ο − (1/48)A²·ν`,
`N₇ = Π + A·ο + (3/16)A²·ν + (5/128)A³·κ`, with their `natDegree`
bounds `a, 2a, 2a, 3a` and their five pure-`A` load columns.  `N₂` is
already in File A.  Data and shapes: `~/lean/tools/sigma810/OPEN_CHAMBERS.md`
§1 and `scripts/derive_810_scale_zero_quartic_open_aux.py`; every column
coefficient here was recomputed from
`scripts/out_810_scale_zero_quartic_coordinates.json`.  Consumed by File D
(the two open chambers, the 19 deep-rescue chambers and the 405 weak-band
walls); nothing in Files B/C depends on it.  Untracked working note.
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

section QuarticAuxTower810

/-! ## The odd `A`-power auxiliaries `N₄, N₅, N₆, N₇`

`N₂ = ν + (1/8)·A·κ` is already in File A.  Each auxiliary cancels one
more level of the odd tower `⟨A³κ, A²ν, Aο, Π⟩`; `N₇` is the deepest
possible member.  `natDegree N ≤ k·a` costs the face equation `2·deg > …`
slack `w − 2k` instead of `w`. -/

set_option maxHeartbeats 64000000 in
/-- `N₄ = Π − A·ο` (weight 17, `natDegree ≤ 1·a`, face slack `15·a > c₀`). -/
def degreeZeroN4Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (-1 : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN4Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN4Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
      A.natDegree := by
  have hb0 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ A.natDegree := by
    rw [hprim]
    omega
  have hb1 : ((-1 : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        A.natDegree + (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [homi, add_zero] at hmul
    omega
  simp only [degreeZeroN4Quartic810]
  exact natDegree_add_le810 hb0 hb1

/-- The pure-`A` `l` column of `N₄`. -/
def n4QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8

/-- The pure-`A` `beta` column of `N₄`. -/
def n4QuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7

/-- The pure-`A` `delta` column of `N₄`. -/
def n4QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6

/-- The pure-`A` `zeta` column of `N₄`. -/
def n4QuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5

/-- The pure-`A` `theta` column of `N₄`. -/
def n4QuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (1 / 4096 * theta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
/-- `N₅ = ο + (1 / 8)·A·ν + (3 / 128)·A²·κ` (weight 15, `natDegree ≤ 2·a`, face slack `11·a > c₀`). -/
def degreeZeroN5Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (1 / 8 : k) • (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (3 / 128 : k) • (A ^ 2 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN5Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN5Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
      2 * A.natDegree := by
  have hb0 : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 2 * A.natDegree := by
    rw [homi]
    omega
  have hb1 : ((1 / 8 : k) • (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 2 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        A.natDegree + (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [hnu, add_zero] at hmul
    omega
  have hb2 : ((3 / 128 : k) • (A ^ 2 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 2 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A ^ 2 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        (A ^ 2).natDegree + (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [hkap, add_zero, natDegree_pow] at hmul
    omega
  simp only [degreeZeroN5Quartic810]
  exact natDegree_add_le810 (natDegree_add_le810 hb0 hb1) hb2

/-- The pure-`A` `l` column of `N₅`. -/
def n5QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7

/-- The pure-`A` `beta` column of `N₅`. -/
def n5QuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6

/-- The pure-`A` `delta` column of `N₅`. -/
def n5QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5

/-- The pure-`A` `zeta` column of `N₅`. -/
def n5QuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4

/-- The pure-`A` `theta` column of `N₅`. -/
def n5QuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * theta : k) • A ^ 3

set_option maxHeartbeats 64000000 in
/-- `N₆ = Π − (2 / 3)·A·ο − (1 / 48)·A²·ν` (weight 17, `natDegree ≤ 2·a`, face slack `13·a > c₀`). -/
def degreeZeroN6Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (-(2 / 3) : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (-(1 / 48) : k) • (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN6Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN6Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
      2 * A.natDegree := by
  have hb0 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 2 * A.natDegree := by
    rw [hprim]
    omega
  have hb1 : ((-(2 / 3) : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 2 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        A.natDegree + (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [homi, add_zero] at hmul
    omega
  have hb2 : ((-(1 / 48) : k) • (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 2 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        (A ^ 2).natDegree + (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [hnu, add_zero, natDegree_pow] at hmul
    omega
  simp only [degreeZeroN6Quartic810]
  exact natDegree_add_le810 (natDegree_add_le810 hb0 hb1) hb2

/-- The pure-`A` `l` column of `N₆`. -/
def n6QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • A ^ 8

/-- The pure-`A` `beta` column of `N₆`. -/
def n6QuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • A ^ 7

/-- The pure-`A` `delta` column of `N₆`. -/
def n6QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 6

/-- The pure-`A` `zeta` column of `N₆`. -/
def n6QuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • A ^ 5

/-- The pure-`A` `theta` column of `N₆`. -/
def n6QuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (5 / 12288 * theta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
/-- `N₇ = Π + A·ο + (3 / 16)·A²·ν + (5 / 128)·A³·κ` (weight 17, `natDegree ≤ 3·a`, face slack `11·a > c₀`). -/
def degreeZeroN7Quartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (1 : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (3 / 16 : k) • (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (5 / 128 : k) • (A ^ 3 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7Quartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN7Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
      3 * A.natDegree := by
  have hb0 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree := by
    rw [hprim]
    omega
  have hb1 : ((1 : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 3 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        A.natDegree + (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [homi, add_zero] at hmul
    omega
  have hb2 : ((3 / 16 : k) • (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 3 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        (A ^ 2).natDegree + (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [hnu, add_zero, natDegree_pow] at hmul
    omega
  have hb3 : ((5 / 128 : k) • (A ^ 3 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ 3 * A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A ^ 3 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        (A ^ 3).natDegree + (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [hkap, add_zero, natDegree_pow] at hmul
    omega
  simp only [degreeZeroN7Quartic810]
  exact natDegree_add_le810 (natDegree_add_le810 (natDegree_add_le810 hb0 hb1) hb2) hb3

/-- The pure-`A` `l` column of `N₇`. -/
def n7QuarticLFace810 (l : k) (A : k[X]) : k[X] :=
  (6435 / 268435456 * l : k) • A ^ 8

/-- The pure-`A` `beta` column of `N₇`. -/
def n7QuarticBetaFace810 (beta : k) (A : k[X]) : k[X] :=
  (429 / 4194304 * beta : k) • A ^ 7

/-- The pure-`A` `delta` column of `N₇`. -/
def n7QuarticDeltaFace810 (delta : k) (A : k[X]) : k[X] :=
  (231 / 524288 * delta : k) • A ^ 6

/-- The pure-`A` `zeta` column of `N₇`. -/
def n7QuarticZetaFace810 (zeta : k) (A : k[X]) : k[X] :=
  (63 / 32768 * zeta : k) • A ^ 5

/-- The pure-`A` `theta` column of `N₇`. -/
def n7QuarticThetaFace810 (theta : k) (A : k[X]) : k[X] :=
  (35 / 4096 * theta : k) • A ^ 4


end QuarticAuxTower810

end Max11DegreeRoutes
