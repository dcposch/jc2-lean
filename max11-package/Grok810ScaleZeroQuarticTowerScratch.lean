import Grok810ScaleZeroQuarticLoadLadderScratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # Auxiliary `A`-power tower and open-chamber certificates, `(8,10)` scale zero

File D1 of the cone-`A` residual.  Imports File A2
(`Grok810ScaleZeroQuarticLoadLadderScratch`; `N₂` already lives in File A)
and the chamber `Prop`s (Defs 1–4) for family-(c) empty walls.

`N₄ = Π − A·ο`, `N₅ = ο + (1/8)A·ν + (3/128)A²·κ`,
`N₆ = Π − (2/3)A·ο − (1/48)A²·ν`,
`N₇ = Π + A·ο + (3/16)A²·ν + (5/128)A³·κ`, each with `natDegree ≤ k·a`
from `natDegree κ = ν = ο = 0` and `natDegree Π = 1`, the load-free /
column splits, and the face-degree side conditions `15a > c`, `11a > c`,
`13a > c`.  Then the two open-chamber certificates (19 and 72 cofactor
terms) and the 19 deep-rescue certificates, each a scalar identity over
`k` followed by the kill `faces = 0`, letters `≠ 0 → False`.  Family (c):
N₇ column kills, empty-wall `omega` lemmas, and the nine `p`-augmented
split patterns.

Data: `~/lean/tools/sigma810/OPEN_CHAMBERS.md` and
`scripts/out_810_scale_zero_quartic_open_*.json`.  Every identity was
checked by `scripts/emit_810_quartic_tower_lean.py` (`expand == 0` and
random points).  No `sorry`, no new axioms, no finite-root shortcut.
Untracked working note.
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

/-! ## The odd `A`-power auxiliaries `N₄, N₅, N₆, N₇`

`N₂ = ν + (1/8)·A·κ` is already in File A.  `natDegree N ≤ k·a`
comes from `natDegree κ = ν = ο = 0` and `natDegree Π = 1 ≤ a`.
-/

section QuarticAuxTower810

set_option maxHeartbeats 64000000 in
/-- `N₄` (weight 17, `natDegree ≤ 1·a`, face slack `15·a > c₀`). -/
def degreeZeroN4TowerQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (-1 : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN4TowerQuartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN4TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
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
  simp only [degreeZeroN4TowerQuartic810]
  exact natDegree_add_le810 hb0 hb1

set_option maxHeartbeats 64000000 in
/-- Face equation of `N₄` is legal once `15 * A.natDegree > c₀`. -/
theorem degreeZeroN4Quartic810_star
    {a c : ℕ}
    (h : c < 15 * a) :
    2 * a < 17 * a - c := by
  have : c ≤ 17 * a := by omega
  omega

/-- The pure-`A` `l` column of `N₄`. -/
def n4QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8

/-- The pure-`A` `beta` column of `N₄`. -/
def n4QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7

/-- The pure-`A` `delta` column of `N₄`. -/
def n4QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6

/-- The pure-`A` `zeta` column of `N₄`. -/
def n4QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5

/-- The pure-`A` `theta` column of `N₄`. -/
def n4QuarticThetaTowerFace810 (theta : k) (A : k[X]) : k[X] :=
  (1 / 4096 * theta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
/-- `N₅` (weight 15, `natDegree ≤ 2·a`, face slack `11·a > c₀`). -/
def degreeZeroN5TowerQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (1 / 8 : k) • (A * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (3 / 128 : k) • (A ^ 2 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN5TowerQuartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN5TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
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
  simp only [degreeZeroN5TowerQuartic810]
  exact natDegree_add_le810 (natDegree_add_le810 hb0 hb1) hb2

set_option maxHeartbeats 64000000 in
/-- Face equation of `N₅` is legal once `11 * A.natDegree > c₀`. -/
theorem degreeZeroN5Quartic810_star
    {a c : ℕ}
    (h : c < 11 * a) :
    4 * a < 15 * a - c := by
  have : c ≤ 15 * a := by omega
  omega

/-- The pure-`A` `l` column of `N₅`. -/
def n5QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7

/-- The pure-`A` `beta` column of `N₅`. -/
def n5QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6

/-- The pure-`A` `delta` column of `N₅`. -/
def n5QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5

/-- The pure-`A` `zeta` column of `N₅`. -/
def n5QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4

/-- The pure-`A` `theta` column of `N₅`. -/
def n5QuarticThetaTowerFace810 (theta : k) (A : k[X]) : k[X] :=
  (5 / 1024 * theta : k) • A ^ 3

set_option maxHeartbeats 64000000 in
/-- `N₆` (weight 17, `natDegree ≤ 2·a`, face slack `13·a > c₀`). -/
def degreeZeroN6TowerQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (-(2 / 3) : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (-(1 / 48) : k) • (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN6TowerQuartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN6TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
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
  simp only [degreeZeroN6TowerQuartic810]
  exact natDegree_add_le810 (natDegree_add_le810 hb0 hb1) hb2

set_option maxHeartbeats 64000000 in
/-- Face equation of `N₆` is legal once `13 * A.natDegree > c₀`. -/
theorem degreeZeroN6Quartic810_star
    {a c : ℕ}
    (h : c < 13 * a) :
    4 * a < 17 * a - c := by
  have : c ≤ 17 * a := by omega
  omega

/-- The pure-`A` `l` column of `N₆`. -/
def n6QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • A ^ 8

/-- The pure-`A` `beta` column of `N₆`. -/
def n6QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • A ^ 7

/-- The pure-`A` `delta` column of `N₆`. -/
def n6QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 6

/-- The pure-`A` `zeta` column of `N₆`. -/
def n6QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • A ^ 5

/-- The pure-`A` `theta` column of `N₆`. -/
def n6QuarticThetaTowerFace810 (theta : k) (A : k[X]) : k[X] :=
  (5 / 12288 * theta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
/-- `N₇` (weight 17, `natDegree ≤ 3·a`, face slack `11·a > c₀`). -/
def degreeZeroN7TowerQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (1 : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (3 / 16 : k) • (A ^ 2 * degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) +
    (5 / 128 : k) • (A ^ 3 * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7TowerQuartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
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
  simp only [degreeZeroN7TowerQuartic810]
  exact natDegree_add_le810 (natDegree_add_le810 (natDegree_add_le810 hb0 hb1) hb2) hb3

set_option maxHeartbeats 64000000 in
/-- Face equation of `N₇` is legal once `11 * A.natDegree > c₀`. -/
theorem degreeZeroN7Quartic810_star
    {a c : ℕ}
    (h : c < 11 * a) :
    6 * a < 17 * a - c := by
  have : c ≤ 17 * a := by omega
  omega

/-- The pure-`A` `l` column of `N₇`. -/
def n7QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (6435 / 268435456 * l : k) • A ^ 8

/-- The pure-`A` `beta` column of `N₇`. -/
def n7QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (429 / 4194304 * beta : k) • A ^ 7

/-- The pure-`A` `delta` column of `N₇`. -/
def n7QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (231 / 524288 * delta : k) • A ^ 6

/-- The pure-`A` `zeta` column of `N₇`. -/
def n7QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (63 / 32768 * zeta : k) • A ^ 5

/-- The pure-`A` `theta` column of `N₇`. -/
def n7QuarticThetaTowerFace810 (theta : k) (A : k[X]) : k[X] :=
  (35 / 4096 * theta : k) • A ^ 4

end QuarticAuxTower810

/-! ## Open-chamber `Prop`s (family (a))

`QuarticOpenChamberI810` is the `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC` cell plus the `ξ`/`π` refinement
`A + D = F`, `D + F = 2B + E`.  `QuarticOpenChamberII810` is the
maximal-tie ray (BUDGET).
-/

section QuarticOpenChambers810

/-- OPEN-I (`BCDEFG#0.2`, the ξ/π sub-cell). -/
def QuarticOpenChamberI810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    2 * D.natDegree < B.natDegree + F.natDegree ∧
    2 * D.natDegree + 2 * E.natDegree < A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < A.natDegree + B.natDegree + F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    A.natDegree + D.natDegree = F.natDegree ∧
    D.natDegree + F.natDegree = 2 * B.natDegree + E.natDegree

/-- OPEN-II (`BCDEFG#0.0`, the maximal-tie ray). -/
def QuarticOpenChamberII810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B ≠ 0 ∧
    C ≠ 0 ∧
    D ≠ 0 ∧
    E ≠ 0 ∧
    F ≠ 0 ∧
    G ≠ 0 ∧
    A.natDegree + 2 * F.natDegree = 2 * G.natDegree ∧
    A.natDegree + 2 * B.natDegree = 2 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = C.natDegree + G.natDegree ∧
    B.natDegree + F.natDegree = 2 * D.natDegree ∧
    A.natDegree + 2 * B.natDegree + 2 * F.natDegree = 2 * D.natDegree + 2 * E.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree ∧
    2 * F.natDegree = A.natDegree + 4 * B.natDegree ∧
    F.natDegree = B.natDegree + C.natDegree ∧
    A.natDegree + 2 * F.natDegree = 4 * C.natDegree ∧
    A.natDegree + B.natDegree + F.natDegree = 3 * C.natDegree ∧
    D.natDegree < A.natDegree + B.natDegree ∧
    2 * D.natDegree + 2 * G.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree ∧
    E.natDegree + G.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree ∧
    F.natDegree < 2 * A.natDegree + B.natDegree ∧
    2 * G.natDegree < 5 * A.natDegree + 2 * B.natDegree ∧
    2 * G.natDegree < 3 * A.natDegree + B.natDegree + F.natDegree ∧
    2 * B.natDegree + 2 * D.natDegree < A.natDegree + 2 * F.natDegree ∧
    B.natDegree + E.natDegree < A.natDegree + F.natDegree ∧
    C.natDegree + D.natDegree < A.natDegree + F.natDegree ∧
    2 * C.natDegree + 2 * E.natDegree < 3 * A.natDegree + 2 * F.natDegree ∧
    4 * C.natDegree + 2 * D.natDegree < 3 * A.natDegree + 2 * B.natDegree + 2 * F.natDegree ∧
    2 * C.natDegree + E.natDegree < 2 * A.natDegree + B.natDegree + F.natDegree

end QuarticOpenChambers810

/-! ## Family (a) — scalar certificates -/

section QuarticOpenCertificates810

def kappaQuarticOpenIFace810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def muQuarticOpenIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

def piQuarticOpenIFace810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def n5QuarticOpenIFace810 (a b c d e f g : k) : k :=
  7 * a * b ^ 3 * c + (-8 : k) * a * b ^ 2 * f + (-36 : k) * b * c ^ 3 + 96 * b * c * g + 64 * c ^ 2 * f
  + (-256 : k) * f * g

def kappaQuarticOpenICofactor810 (a b c d e f g : k) : k :=
  17 * a * b ^ 2 * c * g + (-10 : k) * a * b * c ^ 2 * f + (-16 : k) * a * b * f * g + 16 * a * c * f ^ 2
  + (-20 : k) * c ^ 3 * g + 512 * c * g ^ 2

def muQuarticOpenICofactor810 (a b c d e f g : k) : k :=
  3 * a * b ^ 3 * g + (-6 : k) * a * b ^ 2 * c * f + 8 * a * b * f ^ 2 + (-60 : k) * b * c ^ 2 * g
  + 288 * b * g ^ 2 + 64 * c * f * g

def piQuarticOpenICofactor810 (a b c d e f g : k) : k :=
  (-4 : k) * b * c * g + 8 * f * g

def n5QuarticOpenICofactor810 (a b c d e f g : k) : k :=
  (-2 : k) * a * b ^ 2 * g + 4 * a * b * c * f + (-8 : k) * a * f ^ 2 + 8 * c ^ 2 * g + (-224 : k) * g ^ 2

set_option maxHeartbeats 64000000 in
/-- `65536 · f · g^3 = Σ h_i F_i` on OPEN-I (19 cofactor terms). -/
theorem quarticOpenChamberI810_identity
    (a b c d e f g : k) :
    kappaQuarticOpenICofactor810 a b c d e f g * kappaQuarticOpenIFace810 a b c d e f g +
      muQuarticOpenICofactor810 a b c d e f g * muQuarticOpenIFace810 a b c d e f g +
      piQuarticOpenICofactor810 a b c d e f g * piQuarticOpenIFace810 a b c d e f g +
      n5QuarticOpenICofactor810 a b c d e f g * n5QuarticOpenIFace810 a b c d e f g =
      (65536 : k) * f * g ^ 3 := by
  simp only [kappaQuarticOpenIFace810, muQuarticOpenIFace810, piQuarticOpenIFace810, n5QuarticOpenIFace810,
    kappaQuarticOpenICofactor810, muQuarticOpenICofactor810, piQuarticOpenICofactor810, n5QuarticOpenICofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticOpenChamberI810_impossible
    (a b c d e f g : k)
    (hkap : kappaQuarticOpenIFace810 a b c d e f g = 0)
    (hmu : muQuarticOpenIFace810 a b c d e f g = 0)
    (hpi : piQuarticOpenIFace810 a b c d e f g = 0)
    (hn5 : n5QuarticOpenIFace810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticOpenChamberI810_identity a b c d e f g
  rw [hkap, hmu, hpi, hn5] at hid
  have hsc : (65536 : k) ≠ 0 := by norm_num
  have hprod : (65536 : k) * (f * g ^ 3) = 0 := by
    simpa using hid.symm
  have hz : f * g ^ 3 = 0 := by
    rcases (mul_eq_zero.mp hprod) with h | h
    · exact (hsc h).elim
    · exact h
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    exact (hf hL).elim
  ·
    exact hg ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def kappaQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f + 32 * d * e

def muQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g
  + 16 * e ^ 2

def xiQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e + 32 * e * g

def piQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + 256 * a * b * d * e + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g
  + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

def n2QuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * d * g + 32 * e * f

def n6QuarticOpenIIFace810 (a b c d e f g : k) : k :=
  29 * a * b ^ 3 * c + (-40 : k) * a * b ^ 2 * f + (-80 : k) * a * b * d ^ 2 + (-108 : k) * b * c ^ 3
  + 288 * b * c * g + 320 * b * e ^ 2 + 128 * c ^ 2 * f + 608 * c * d * e + (-1280 : k) * f * g

def kappaQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  (-25080 : k) * a ^ 2 * b ^ 3 * d * f + 291480 * a ^ 2 * b ^ 2 * d ^ 3
  + (-433136 : k) * a * b ^ 2 * c * d * g + (-8095920 : k) * a * b ^ 2 * d * e ^ 2
  + (-1167232 : k) * a * b * c ^ 2 * d * f + (-14803488 : k) * a * b * c * d ^ 2 * e
  + (-6960640 : k) * a * b * d * f * g + 694176 * a * c ^ 2 * d ^ 3 + 650496 * a * c * d * f ^ 2
  + 4620000 * a * d ^ 3 * g + 27720000 * a * d ^ 2 * e * f + 2535104 * c ^ 3 * d * g
  + 24943296 * c ^ 2 * d * e ^ 2 + (-2601984 : k) * c * d * g ^ 2 + 83699712 * c * e * f * g
  + (-92400000 : k) * d * e ^ 2 * g

def muQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  (-731280 : k) * a * b ^ 3 * d * g + (-1362240 : k) * a * b ^ 2 * c * d * f
  + (-5103840 : k) * a * b ^ 2 * d ^ 2 * e + (-1985340 : k) * a * b * c * d ^ 3 + 880000 * a * b * d * f ^ 2
  + 6930000 * a * d ^ 3 * f + 2122560 * b * c ^ 2 * d * g + 49521360 * b * c * d * e ^ 2
  + (-3520000 : k) * b * d * g ^ 2 + 88104960 * b * e * f * g + (-401280 : k) * c ^ 3 * d * f
  + 37047360 * c ^ 2 * d ^ 2 * e + 27842560 * c * d * f * g + (-110880000 : k) * d ^ 2 * e * g
  + (-83160000 : k) * d * e ^ 2 * f

def xiQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  2552900 * a * b ^ 3 * d * e + 1306200 * a * b ^ 2 * c * d ^ 2 + (-3909040 : k) * a * b * d ^ 2 * f
  + (-3465000 : k) * a * d ^ 4 + (-28324800 : k) * b * c ^ 2 * d * e + (-36710400 : k) * b * c * f * g
  + 80316160 * b * d * e * g + (-971600 : k) * c ^ 3 * d ^ 2 + 12556160 * c * d ^ 2 * g
  + 77236160 * c * d * e * f + 106260000 * d ^ 2 * e ^ 2 + 127262720 * f ^ 2 * g

def piQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  8360 * a * b ^ 2 * d * f + (-36435 : k) * a * b * d ^ 3 + (-66880 : k) * b * c * d * g
  + 145740 * b * d * e ^ 2 + (-33440 : k) * c ^ 2 * d * f + 291480 * c * d ^ 2 * e
  + (-2829440 : k) * d * f * g

def n2QuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  (-60725 : k) * a ^ 2 * b ^ 3 * d ^ 2 + 7081200 * a * b ^ 2 * c * d * e + 4588800 * a * b ^ 2 * f * g
  + 1306200 * a * b * c ^ 2 * d ^ 2 + (-1599040 : k) * a * b * d ^ 2 * g
  + (-17769040 : k) * a * b * d * e * f + (-2369040 : k) * a * c * d ^ 2 * f
  + (-15015000 : k) * a * d ^ 3 * e + (-10211600 : k) * c ^ 3 * d * e + (-18355200 : k) * c ^ 2 * f * g
  + 74156160 * c * d * e * g + 41580000 * d * e ^ 3 + 127262720 * f * g ^ 2

def n6QuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  97504 * a * b ^ 2 * d * g + 195008 * a * b * c * d * f + (-437808 : k) * a * b * d ^ 2 * e
  + (-218904 : k) * a * c * d ^ 3 + (-229504 : k) * a * d * f ^ 2 + (-390016 : k) * c ^ 2 * d * g
  + 875616 * c * d * e ^ 2 + 918016 * d * g ^ 2 + (-4405248 : k) * e * f * g

def quarticOpenChamberII810_identityPartial1 (a b c d e f g : k) : k :=
  (-25080 : k) * a ^ 3 * b ^ 6 * d * f + 291480 * a ^ 3 * b ^ 5 * d ^ 3
  + (-2626976 : k) * a ^ 2 * b ^ 5 * c * d * g + (-8095920 : k) * a ^ 2 * b ^ 5 * d * e ^ 2
  + (-4952992 : k) * a ^ 2 * b ^ 4 * c ^ 2 * d * f + (-30115008 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + (-1912960 : k) * a ^ 2 * b ^ 4 * d * f * g + (-8759604 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + 13385856 * a ^ 2 * b ^ 3 * c * d * f ^ 2 + 16872480 * a ^ 2 * b ^ 3 * d ^ 3 * g
  + 67748160 * a ^ 2 * b ^ 3 * d ^ 2 * e * f + 51449040 * a ^ 2 * b ^ 2 * c * d ^ 3 * f
  + 29742720 * a ^ 2 * b ^ 2 * d ^ 4 * e + (-7040000 : k) * a ^ 2 * b ^ 2 * d * f ^ 3
  + 7941360 * a ^ 2 * b * c * d ^ 5 + (-58960000 : k) * a ^ 2 * b * d ^ 3 * f ^ 2
  + (-27720000 : k) * a ^ 2 * d ^ 5 * f + 17025536 * a * b ^ 3 * c ^ 3 * d * g
  + 270658416 * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (-50423296 : k) * a * b ^ 3 * c * d * g ^ 2
  + 348014592 * a * b ^ 3 * c * e * f * g + (-363169920 : k) * a * b ^ 3 * d * e ^ 2 * g
  + 18251904 * a * b ^ 2 * c ^ 4 * d * f + 309199296 * a * b ^ 2 * c ^ 3 * d ^ 2 * e
  + 55271424 * a * b ^ 2 * c ^ 2 * d * f * g + (-983534848 : k) * a * b ^ 2 * c * d ^ 2 * e * g
  + (-926516160 : k) * a * b ^ 2 * c * d * e ^ 2 * f + (-340730880 : k) * a * b ^ 2 * d ^ 2 * e ^ 3
  + (-194580480 : k) * a * b ^ 2 * d * f * g ^ 2 + (-704839680 : k) * a * b ^ 2 * e * f ^ 2 * g
  + (-388752 : k) * a * b * c ^ 4 * d ^ 3 + (-45467136 : k) * a * b * c ^ 3 * d * f ^ 2
  + (-105247488 : k) * a * b * c ^ 2 * d ^ 3 * g + (-1140081920 : k) * a * b * c ^ 2 * d ^ 2 * e * f
  + (-703562496 : k) * a * b * c * d ^ 3 * e ^ 2 + (-396505088 : k) * a * b * c * d * f ^ 2 * g
  + 161920000 * a * b * d ^ 3 * g ^ 2 + 1198919680 * a * b * d ^ 2 * e * f * g
  + 679360000 * a * b * d * e ^ 2 * f ^ 2 + (-3901248 : k) * a * c ^ 3 * d ^ 3 * f
  + (-125975808 : k) * a * c ^ 2 * d ^ 4 * e + 20815872 * a * c ^ 2 * d * f ^ 3
  + 258229760 * a * c * d ^ 3 * f * g + 907855872 * a * c * d ^ 2 * e * f ^ 2
  + 591360000 * a * d ^ 4 * e * g + 1330560000 * a * d ^ 3 * e ^ 2 * f + (-38911488 : k) * b * c ^ 5 * d * g
  + (-497404992 : k) * b * c ^ 4 * d * e ^ 2 + 194349056 * b * c ^ 3 * d * g ^ 2
  + (-1356816384 : k) * b * c ^ 3 * e * f * g + 3525629952 * b * c ^ 2 * d * e ^ 2 * g
  + 792341760 * b * c * d * e ^ 4 + (-195903488 : k) * b * c * d * g ^ 3
  + 5497749504 * b * c * e * f * g ^ 2 + (-3013120000 : k) * b * d * e ^ 2 * g ^ 2
  + 1409679360 * b * e ^ 3 * f * g + 1605120 * c ^ 6 * d * f + (-148189440 : k) * c ^ 5 * d ^ 2 * e
  + (-43087872 : k) * c ^ 4 * d * f * g + 1710158848 * c ^ 3 * d ^ 2 * e * g
  + 1124404992 * c ^ 3 * d * e ^ 2 * f + 1390943232 * c ^ 2 * d ^ 2 * e ^ 3
  + 807698432 * c ^ 2 * d * f * g ^ 2 + 2678390784 * c ^ 2 * e * f ^ 2 * g
  + (-3631423488 : k) * c * d ^ 2 * e * g ^ 2 + (-2494048256 : k) * c * d * e ^ 2 * f * g
  + (-4730880000 : k) * d ^ 2 * e ^ 3 * g + (-1330560000 : k) * d * e ^ 4 * f

def quarticOpenChamberII810_identityPartial2 (a b c d e f g : k) : k :=
  25080 * a ^ 3 * b ^ 6 * d * f + (-109305 : k) * a ^ 3 * b ^ 5 * d ^ 3
  + (-200640 : k) * a ^ 2 * b ^ 5 * c * d * g + 8095920 * a ^ 2 * b ^ 5 * d * e ^ 2
  + (-702240 : k) * a ^ 2 * b ^ 4 * c ^ 2 * d * f + 20110440 * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + (-7953280 : k) * a ^ 2 * b ^ 4 * d * f * g + 10460520 * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + 1070080 * a ^ 2 * b ^ 3 * c * d * f ^ 2 + (-2331840 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g
  + (-30010160 : k) * a ^ 2 * b ^ 3 * d ^ 2 * e * f + (-37497440 : k) * a ^ 2 * b ^ 2 * c * d ^ 3 * f
  + (-19722360 : k) * a ^ 2 * b ^ 2 * d ^ 4 * e + (-2140160 : k) * a ^ 2 * b ^ 2 * d * f ^ 3
  + (-25453680 : k) * a ^ 2 * b * c * d ^ 5 + 40599680 * a ^ 2 * b * d ^ 3 * f ^ 2
  + 27720000 * a ^ 2 * d ^ 5 * f + 4815360 * a * b ^ 3 * c ^ 3 * d * g
  + (-126102480 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (-4280320 : k) * a * b ^ 3 * c * d * g ^ 2
  + (-110131200 : k) * a * b ^ 3 * c * e * f * g + 331968640 * a * b ^ 3 * d * e ^ 2 * g
  + 2808960 * a * b ^ 2 * c ^ 4 * d * f + (-209524560 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e
  + (-29383680 : k) * a * b ^ 2 * c ^ 2 * d * f * g + 562897280 * a * b ^ 2 * c * d ^ 2 * e * g
  + 246082880 * a * b ^ 2 * c * d * e ^ 2 * f + 356089440 * a * b ^ 2 * d ^ 2 * e ^ 3
  + (-172523520 : k) * a * b ^ 2 * d * f * g ^ 2 + 381788160 * a * b ^ 2 * e * f ^ 2 * g
  + (-7578480 : k) * a * b * c ^ 4 * d ^ 3 + (-4280320 : k) * a * b * c ^ 3 * d * f ^ 2
  + 76103680 * a * b * c ^ 2 * d ^ 3 * g + 765672640 * a * b * c ^ 2 * d ^ 2 * e * f
  + 749488320 * a * b * c * d ^ 3 * e ^ 2 + 712212480 * a * b * c * d * f ^ 2 * g
  + (-37309440 : k) * a * b * d ^ 3 * g ^ 2 + (-1491955200 : k) * a * b * d ^ 2 * e * f * g
  + (-37309440 : k) * a * b * d * e ^ 2 * f ^ 2 + 3492480 * a * c ^ 3 * d ^ 3 * f
  + 78889440 * a * c ^ 2 * d ^ 4 * e + 8560640 * a * c ^ 2 * d * f ^ 3
  + (-462617600 : k) * a * c * d ^ 3 * f * g + (-692508160 : k) * a * c * d ^ 2 * e * f ^ 2
  + (-110880000 : k) * a * d ^ 4 * e * g + (-850080000 : k) * a * d ^ 3 * e ^ 2 * f
  + (-293765120 : k) * a * d * f ^ 3 * g + (-3210240 : k) * b * c ^ 5 * d * g
  + 346893120 * b * c ^ 4 * d * e ^ 2 + 17121280 * b * c ^ 3 * d * g ^ 2 + 440524800 * b * c ^ 3 * e * f * g
  + (-1873254400 : k) * b * c ^ 2 * d * e ^ 2 * g + (-74618880 : k) * b * c * d * e ^ 4
  + (-68485120 : k) * b * c * d * g ^ 3 + (-1174732800 : k) * b * c * e * f * g ^ 2
  + 2719354880 * b * d * e ^ 2 * g ^ 2 + (-1605120 : k) * c ^ 6 * d * f + 25650240 * c ^ 5 * d ^ 2 * e
  + (-127252480 : k) * c ^ 4 * d * f * g + (-256384000 : k) * c ^ 3 * d ^ 2 * e * g
  + (-909712640 : k) * c ^ 3 * d * e ^ 2 * f + (-1424357760 : k) * c ^ 2 * d ^ 2 * e ^ 3
  + 690094080 * c ^ 2 * d * f * g ^ 2 + (-1527152640 : k) * c ^ 2 * e * f ^ 2 * g
  + 700272640 * c * d ^ 2 * e * g ^ 2 + 3920230400 * c * d * e ^ 2 * f * g + 3400320000 * d ^ 2 * e ^ 3 * g
  + (-2897346560 : k) * d * f * g ^ 3 + 4072407040 * e * f ^ 2 * g ^ 2

def quarticOpenChamberII810_identityPartial3 (a b c d e f g : k) : k :=
  (-182175 : k) * a ^ 3 * b ^ 5 * d ^ 3 + 2827616 * a ^ 2 * b ^ 5 * c * d * g
  + 5655232 * a ^ 2 * b ^ 4 * c ^ 2 * d * f + 10004568 * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + 9866240 * a ^ 2 * b ^ 4 * d * f * g + (-1700916 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (-14455936 : k) * a ^ 2 * b ^ 3 * c * d * f ^ 2 + (-14540640 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g
  + (-37738000 : k) * a ^ 2 * b ^ 3 * d ^ 2 * e * f + (-13951600 : k) * a ^ 2 * b ^ 2 * c * d ^ 3 * f
  + (-10020360 : k) * a ^ 2 * b ^ 2 * d ^ 4 * e + 9180160 * a ^ 2 * b ^ 2 * d * f ^ 3
  + 17512320 * a ^ 2 * b * c * d ^ 5 + 18360320 * a ^ 2 * b * d ^ 3 * f ^ 2
  + (-21840896 : k) * a * b ^ 3 * c ^ 3 * d * g + (-144555936 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2
  + 54703616 * a * b ^ 3 * c * d * g ^ 2 + (-237883392 : k) * a * b ^ 3 * c * e * f * g
  + 31201280 * a * b ^ 3 * d * e ^ 2 * g + (-21060864 : k) * a * b ^ 2 * c ^ 4 * d * f
  + (-99674736 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-25887744 : k) * a * b ^ 2 * c ^ 2 * d * f * g
  + 420637568 * a * b ^ 2 * c * d ^ 2 * e * g + 680433280 * a * b ^ 2 * c * d * e ^ 2 * f
  + (-15358560 : k) * a * b ^ 2 * d ^ 2 * e ^ 3 + 367104000 * a * b ^ 2 * d * f * g ^ 2
  + 323051520 * a * b ^ 2 * e * f ^ 2 * g + 7967232 * a * b * c ^ 4 * d ^ 3
  + 49747456 * a * b * c ^ 3 * d * f ^ 2 + 29143808 * a * b * c ^ 2 * d ^ 3 * g
  + 374409280 * a * b * c ^ 2 * d ^ 2 * e * f + (-45925824 : k) * a * b * c * d ^ 3 * e ^ 2
  + (-315707392 : k) * a * b * c * d * f ^ 2 * g + (-124610560 : k) * a * b * d ^ 3 * g ^ 2
  + 293035520 * a * b * d ^ 2 * e * f * g + (-642050560 : k) * a * b * d * e ^ 2 * f ^ 2
  + 408768 * a * c ^ 3 * d ^ 3 * f + 47086368 * a * c ^ 2 * d ^ 4 * e
  + (-29376512 : k) * a * c ^ 2 * d * f ^ 3 + 204387840 * a * c * d ^ 3 * f * g
  + (-215347712 : k) * a * c * d ^ 2 * e * f ^ 2 + (-480480000 : k) * a * d ^ 4 * e * g
  + (-480480000 : k) * a * d ^ 3 * e ^ 2 * f + 293765120 * a * d * f ^ 3 * g + 42121728 * b * c ^ 5 * d * g
  + 150511872 * b * c ^ 4 * d * e ^ 2 + (-211470336 : k) * b * c ^ 3 * d * g ^ 2
  + 916291584 * b * c ^ 3 * e * f * g + (-1652375552 : k) * b * c ^ 2 * d * e ^ 2 * g
  + (-717722880 : k) * b * c * d * e ^ 4 + 264388608 * b * c * d * g ^ 3
  + (-4323016704 : k) * b * c * e * f * g ^ 2 + 293765120 * b * d * e ^ 2 * g ^ 2
  + (-1409679360 : k) * b * e ^ 3 * f * g + 122539200 * c ^ 5 * d ^ 2 * e + 170340352 * c ^ 4 * d * f * g
  + (-1453774848 : k) * c ^ 3 * d ^ 2 * e * g + (-214692352 : k) * c ^ 3 * d * e ^ 2 * f
  + 33414528 * c ^ 2 * d ^ 2 * e ^ 3 + (-1497792512 : k) * c ^ 2 * d * f * g ^ 2
  + (-1151238144 : k) * c ^ 2 * e * f ^ 2 * g + 2931150848 * c * d ^ 2 * e * g ^ 2
  + (-1426182144 : k) * c * d * e ^ 2 * f * g + 1330560000 * d ^ 2 * e ^ 3 * g + 1330560000 * d * e ^ 4 * f
  + 2897346560 * d * f * g ^ 3 + 9711124480 * e * f ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
/-- `13783531520 · e · f^2 · g^2 = Σ h_i F_i` on OPEN-II (72 cofactor terms). -/
theorem quarticOpenChamberII810_identity
    (a b c d e f g : k) :
    (((kappaQuarticOpenIICofactor810 a b c d e f g * kappaQuarticOpenIIFace810 a b c d e f g + muQuarticOpenIICofactor810 a b c d e f g * muQuarticOpenIIFace810 a b c d e f g) +
      (xiQuarticOpenIICofactor810 a b c d e f g * xiQuarticOpenIIFace810 a b c d e f g + piQuarticOpenIICofactor810 a b c d e f g * piQuarticOpenIIFace810 a b c d e f g)) +
      (n2QuarticOpenIICofactor810 a b c d e f g * n2QuarticOpenIIFace810 a b c d e f g + n6QuarticOpenIICofactor810 a b c d e f g * n6QuarticOpenIIFace810 a b c d e f g)) =
      (13783531520 : k) * (e * f ^ 2 * g ^ 2) := by
  have h1 : kappaQuarticOpenIICofactor810 a b c d e f g * kappaQuarticOpenIIFace810 a b c d e f g + muQuarticOpenIICofactor810 a b c d e f g * muQuarticOpenIIFace810 a b c d e f g = quarticOpenChamberII810_identityPartial1 a b c d e f g := by
    simp only [kappaQuarticOpenIICofactor810, kappaQuarticOpenIIFace810, muQuarticOpenIICofactor810, muQuarticOpenIIFace810, quarticOpenChamberII810_identityPartial1]
    ring
  have h2 : xiQuarticOpenIICofactor810 a b c d e f g * xiQuarticOpenIIFace810 a b c d e f g + piQuarticOpenIICofactor810 a b c d e f g * piQuarticOpenIIFace810 a b c d e f g = quarticOpenChamberII810_identityPartial2 a b c d e f g := by
    simp only [xiQuarticOpenIICofactor810, xiQuarticOpenIIFace810, piQuarticOpenIICofactor810, piQuarticOpenIIFace810, quarticOpenChamberII810_identityPartial2]
    ring
  have h3 : n2QuarticOpenIICofactor810 a b c d e f g * n2QuarticOpenIIFace810 a b c d e f g + n6QuarticOpenIICofactor810 a b c d e f g * n6QuarticOpenIIFace810 a b c d e f g = quarticOpenChamberII810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticOpenIICofactor810, n2QuarticOpenIIFace810, n6QuarticOpenIICofactor810, n6QuarticOpenIIFace810, quarticOpenChamberII810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticOpenChamberII810_identityPartial1, quarticOpenChamberII810_identityPartial2, quarticOpenChamberII810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticOpenChamberII810_impossible
    (a b c d e f g : k)
    (hkap : kappaQuarticOpenIIFace810 a b c d e f g = 0)
    (hmu : muQuarticOpenIIFace810 a b c d e f g = 0)
    (hxi : xiQuarticOpenIIFace810 a b c d e f g = 0)
    (hpi : piQuarticOpenIIFace810 a b c d e f g = 0)
    (hn2 : n2QuarticOpenIIFace810 a b c d e f g = 0)
    (hn6 : n6QuarticOpenIIFace810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticOpenChamberII810_identity a b c d e f g
  rw [hkap, hmu, hxi, hpi, hn2, hn6] at hid
  have hsc : (13783531520 : k) ≠ 0 := by norm_num
  have hprod : (13783531520 : k) * (e * f ^ 2 * g ^ 2) = 0 := by
    simpa using hid.symm
  have hz : e * f ^ 2 * g ^ 2 = 0 := by
    rcases (mul_eq_zero.mp hprod) with h | h
    · exact (hsc h).elim
    · exact h
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (he hLl).elim
    ·
      exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRl)
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

end QuarticOpenCertificates810

/-! ## Family (b) — the 19 deep-rescue scalar certificates -/

section QuarticRescueCertificates810

def muQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 16 * e ^ 2

def muQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 3410 : k) * b ^ 2 * c * e * f + (-9 / 1364 : k) * b ^ 2 * d * e ^ 2
  + (-681 / 13640 : k) * b * c ^ 2 * d * f + (-27 / 1705 : k) * b * c * d ^ 2 * e
  + (-16 / 1705 : k) * b * e * f ^ 2 + (-9 / 1705 : k) * c ^ 2 * d ^ 3 + (1143 / 27280 : k) * c * d * f ^ 2
  + (3369 / 54560 : k) * d ^ 2 * e * f

def xiQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e

def xiQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 2728 : k) * b ^ 3 * e ^ 2 + (1059 / 109120 : k) * b ^ 2 * c ^ 2 * f
  + (3 / 682 : k) * b ^ 2 * c * d * e + (9 / 2728 : k) * b * c ^ 2 * d ^ 2
  + (-549 / 13640 : k) * b * c * f ^ 2 + (-189 / 109120 : k) * b * d * e * f
  + (131 / 109120 : k) * c * d ^ 2 * f + (-3 / 682 : k) * d ^ 3 * e + (131 / 6820 : k) * f ^ 3

def piQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 128 * a * b * c * f + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-512 : k) * c * e ^ 2

def piQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * b ^ 2 * e * f + (-741 / 436480 : k) * b * c * d * f + (-27 / 54560 : k) * b * d ^ 2 * e
  + (-9 / 54560 : k) * c * d ^ 3 + (-131 / 218240 : k) * d * f ^ 2

def kappaQuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * c * f + 32 * d * e

def kappaQuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (9 / 27280 : k) * a * b ^ 3 * e * f + (435 / 87296 : k) * a * b ^ 2 * c * d * f
  + (27 / 6820 : k) * a * b ^ 2 * d ^ 2 * e + (117 / 54560 : k) * a * b * c * d ^ 3
  + (921 / 54560 : k) * a * b * d * f ^ 2 + (2889 / 436480 : k) * a * d ^ 3 * f
  + (9 / 2728 : k) * b ^ 2 * e ^ 3 + (-645 / 21824 : k) * b * c ^ 2 * e * f
  + (-9 / 2728 : k) * b * c * d * e ^ 2 + (-9 / 2728 : k) * c ^ 2 * d ^ 2 * e
  + (643 / 27280 : k) * c * e * f ^ 2 + (-2889 / 109120 : k) * d * e ^ 2 * f

def n2QuarticCostChamberBCDEF1Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * e * f

def n2QuarticCostChamberBCDEF1Cofactor810 (a b c d e f g : k) : k :=
  (1 / 27280 : k) * a * b ^ 3 * c * f + (-9 / 10912 : k) * a * b ^ 3 * d * e
  + (-3 / 5456 : k) * a * b ^ 2 * c * d ^ 2 + (-1097 / 218240 : k) * a * b ^ 2 * f ^ 2
  + (-963 / 436480 : k) * a * b * d ^ 2 * f + (-3 / 2728 : k) * b ^ 2 * c * e ^ 2
  + (215 / 21824 : k) * b * c ^ 3 * f + (3 / 2728 : k) * b * c ^ 2 * d * e + (8 / 1705 : k) * b * e ^ 2 * f
  + (3 / 2728 : k) * c ^ 3 * d ^ 2 + (-893 / 54560 : k) * c ^ 2 * f ^ 2
  + (-3017 / 109120 : k) * c * d * e * f + (-3 / 682 : k) * d ^ 2 * e ^ 2

def quarticCostChamberBCDEF1810_identityPartial1 (a b c d e f g : k) : k :=
  (-9 / 2728 : k) * a * b ^ 5 * e ^ 3 + (2889 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f
  + (-9 / 682 : k) * a * b ^ 4 * c * d * e ^ 2 + (-999 / 10912 : k) * a * b ^ 3 * c ^ 3 * d * f
  + (-153 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (-387 / 2728 : k) * a * b ^ 3 * c * e * f ^ 2
  + (6153 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 6820 : k) * a * b ^ 2 * c ^ 3 * d ^ 3
  + (5619 / 27280 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2
  + (29841 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2
  + (181 / 1364 : k) * a * b ^ 2 * e * f ^ 3 + (12153 / 54560 : k) * a * b * c ^ 2 * d ^ 3 * f
  + (63 / 1705 : k) * a * b * c * d ^ 4 * e + (174 / 1705 : k) * a * b * c * d * f ^ 3
  + (-6037 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2 + (36 / 1705 : k) * a * c ^ 2 * d ^ 5
  + (-2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2 + (-2889 / 13640 : k) * a * d ^ 4 * e * f
  + (-262 / 1705 : k) * a * d * f ^ 4 + (9 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3
  + (-3081 / 27280 : k) * b ^ 2 * c ^ 4 * e * f + (-9 / 341 : k) * b ^ 2 * c ^ 3 * d * e ^ 2
  + (-24 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (-36 / 341 : k) * b ^ 2 * d * e ^ 4
  + (681 / 3410 : k) * b * c ^ 5 * d * f + (81 / 3410 : k) * b * c ^ 4 * d ^ 2 * e
  + (355 / 682 : k) * b * c ^ 3 * e * f ^ 2 + (-4245 / 5456 : k) * b * c ^ 2 * d * e ^ 2 * f
  + (-432 / 1705 : k) * b * c * d ^ 2 * e ^ 3 + (-256 / 1705 : k) * b * e ^ 3 * f ^ 2
  + (36 / 1705 : k) * c ^ 5 * d ^ 3 + (-1143 / 6820 : k) * c ^ 4 * d * f ^ 2
  + (-7131 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (-54 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2
  + (-393 / 1705 : k) * c ^ 2 * e * f ^ 3 + (1143 / 1705 : k) * c * d * e ^ 2 * f ^ 2
  + (3369 / 3410 : k) * d ^ 2 * e ^ 3 * f

def quarticCostChamberBCDEF1810_identityPartial2 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e
  + (9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2
  + (2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (9 / 2728 : k) * a * b ^ 5 * e ^ 3
  + (-2793 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f + (-9 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2
  + (6813 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f + (-207 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e
  + (547 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2 + (-4809 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f
  + (-189 / 13640 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (-1185 / 5456 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2
  + (-3081 / 13640 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (48 / 1705 : k) * a * b ^ 2 * e * f ^ 3
  + (-5439 / 21824 : k) * a * b * c ^ 2 * d ^ 3 * f + (-63 / 1705 : k) * a * b * c * d ^ 4 * e
  + (1531 / 1705 : k) * a * b * c * d * f ^ 3 + (175 / 341 : k) * a * b * d ^ 2 * e * f ^ 2
  + (-36 / 1705 : k) * a * c ^ 2 * d ^ 5 + (2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2
  + (2889 / 13640 : k) * a * d ^ 4 * e * f + (262 / 1705 : k) * a * d * f ^ 4
  + (-27 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (9531 / 27280 : k) * b ^ 2 * c ^ 4 * e * f
  + (27 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (276 / 1705 : k) * b ^ 2 * c * e ^ 3 * f
  + (36 / 341 : k) * b ^ 2 * d * e ^ 4 + (-2223 / 27280 : k) * b * c ^ 5 * d * f
  + (27 / 1705 : k) * b * c ^ 4 * d ^ 2 * e + (-8379 / 6820 : k) * b * c ^ 3 * e * f ^ 2
  + (3699 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * f + (252 / 1705 : k) * b * c * d ^ 2 * e ^ 3
  + (-27 / 3410 : k) * c ^ 5 * d ^ 3 + (-393 / 13640 : k) * c ^ 4 * d * f ^ 2
  + (-36 / 341 : k) * c ^ 3 * d ^ 2 * e * f + (-36 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2
  + (1286 / 1705 : k) * c ^ 2 * e * f ^ 3 + (731 / 3410 : k) * c * d * e ^ 2 * f ^ 2
  + (-2889 / 3410 : k) * d ^ 2 * e ^ 3 * f

def quarticCostChamberBCDEF1810_identityPartial3 (a b c d e f g : k) : k :=
  (3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (-27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e
  + (-9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (-3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2
  + (-2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (-3 / 3410 : k) * a * b ^ 4 * c ^ 2 * e * f
  + (45 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2 + (3177 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f
  + (9 / 341 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (3323 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2
  + (-21 / 1705 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 2728 : k) * a * b ^ 2 * c ^ 3 * d ^ 3
  + (153 / 13640 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (-5193 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f
  + (-9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2 + (-1097 / 6820 : k) * a * b ^ 2 * e * f ^ 3
  + (2889 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * f + (-963 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2
  + (9 / 341 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (-645 / 2728 : k) * b ^ 2 * c ^ 4 * e * f
  + (-9 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (-252 / 1705 : k) * b ^ 2 * c * e ^ 3 * f
  + (-645 / 5456 : k) * b * c ^ 5 * d * f + (-27 / 682 : k) * b * c ^ 4 * d ^ 2 * e
  + (439 / 620 : k) * b * c ^ 3 * e * f ^ 2 + (8763 / 13640 : k) * b * c ^ 2 * d * e ^ 2 * f
  + (36 / 341 : k) * b * c * d ^ 2 * e ^ 3 + (256 / 1705 : k) * b * e ^ 3 * f ^ 2
  + (-9 / 682 : k) * c ^ 5 * d ^ 3 + (2679 / 13640 : k) * c ^ 4 * d * f ^ 2
  + (10011 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (18 / 341 : k) * c ^ 2 * d ^ 3 * e ^ 2
  + (-893 / 1705 : k) * c ^ 2 * e * f ^ 3 + (-3017 / 3410 : k) * c * d * e ^ 2 * f ^ 2
  + (-48 / 341 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #1: `BCDEF` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*c*d*f^3`, 47 cofactor terms. -/
theorem quarticCostChamberBCDEF1810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * muQuarticCostChamberBCDEF1Face810 a b c d e f g + xiQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEF1Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * piQuarticCostChamberBCDEF1Face810 a b c d e f g + kappaQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEF1Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEF1Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEF1Face810 a b c d e f g)) =
      a * b * c * d * f ^ 3 := by
  have h1 : muQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * muQuarticCostChamberBCDEF1Face810 a b c d e f g + xiQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEF1Face810 a b c d e f g = quarticCostChamberBCDEF1810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEF1Cofactor810, muQuarticCostChamberBCDEF1Face810, xiQuarticCostChamberBCDEF1Cofactor810, xiQuarticCostChamberBCDEF1Face810, quarticCostChamberBCDEF1810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * piQuarticCostChamberBCDEF1Face810 a b c d e f g + kappaQuarticCostChamberBCDEF1Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEF1Face810 a b c d e f g = quarticCostChamberBCDEF1810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEF1Cofactor810, piQuarticCostChamberBCDEF1Face810, kappaQuarticCostChamberBCDEF1Cofactor810, kappaQuarticCostChamberBCDEF1Face810, quarticCostChamberBCDEF1810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEF1Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEF1Face810 a b c d e f g = quarticCostChamberBCDEF1810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEF1Cofactor810, n2QuarticCostChamberBCDEF1Face810, quarticCostChamberBCDEF1810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEF1810_identityPartial1, quarticCostChamberBCDEF1810_identityPartial2, quarticCostChamberBCDEF1810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEF1810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEF1Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEF1810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c * d * f ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact (hc hRll).elim
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (-69 / 917504 : k) * a ^ 2 * b ^ 3 * c * d + (347 / 229376 : k) * a ^ 2 * b ^ 2 * d * f
  + (-87 / 458752 : k) * a * b ^ 2 * c ^ 2 * e + (-577 / 28672 : k) * a * b ^ 2 * e * g
  + (2253 / 458752 : k) * a * b * c ^ 3 * d + (719 / 57344 : k) * a * b * c * d * g
  + (-1047 / 114688 : k) * a * b * c * e * f + (297 / 114688 : k) * a * c ^ 2 * d * f
  + (143 / 6144 : k) * a * d * f * g + (-81 / 2048 : k) * a * e * f ^ 2 + (7 / 2048 : k) * c ^ 2 * e * g
  + (13 / 384 : k) * e * g ^ 2

def xiQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e + 32 * e * g

def xiQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (69 / 917504 : k) * a ^ 2 * b ^ 4 * c + (127 / 65536 : k) * a ^ 2 * b ^ 3 * f
  + (-275 / 229376 : k) * a * b ^ 2 * c ^ 3 + (543 / 57344 : k) * a * b ^ 2 * c * g
  + (-1921 / 114688 : k) * a * b * c ^ 2 * f + (433 / 10752 : k) * a * b * f * g
  + (331 / 3584 : k) * a * c * f ^ 2 + (-5 / 768 : k) * c ^ 3 * g + (7 / 768 : k) * c * g ^ 2

def piQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (63 / 262144 : k) * a * b ^ 2 * c * e + (1 / 262144 : k) * a * b * c ^ 2 * d
  + (1 / 512 : k) * a * b * d * g + (65 / 65536 : k) * a * b * e * f + (85 / 65536 : k) * a * c * d * f
  + (-11 / 8192 : k) * c * e * g

def kappaQuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (-1737 / 1835008 : k) * a ^ 2 * b ^ 3 * c * e + (1581 / 1835008 : k) * a ^ 2 * b ^ 2 * c ^ 2 * d
  + (-9 / 1024 : k) * a ^ 2 * b ^ 2 * e * f + (-6513 / 458752 : k) * a ^ 2 * b * c * d * f
  + (1919 / 57344 : k) * a ^ 2 * d * f ^ 2 + (255 / 114688 : k) * a * b * c ^ 3 * e
  + (93 / 57344 : k) * a * b * c * e * g + (-93 / 57344 : k) * a * c ^ 4 * d
  + (65 / 7168 : k) * a * c ^ 2 * d * g + (3405 / 114688 : k) * a * c ^ 2 * e * f
  + (-1 / 16 : k) * a * d * g ^ 2 + (-911 / 14336 : k) * a * e * f * g

def n4QuarticCostChamberBCDEFG2Face810 (a b c d e f g : k) : k :=
  3 * a ^ 3 * b ^ 2 * d + (-24 : k) * a ^ 2 * b * c * e + (-12 : k) * a ^ 2 * c ^ 2 * d + 32 * a ^ 2 * d * g
  + 32 * a ^ 2 * e * f

def n4QuarticCostChamberBCDEFG2Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 8192 : k) * b ^ 3 * c ^ 2 + (-1 / 512 : k) * b ^ 3 * g + (-1 / 512 : k) * b ^ 2 * c * f
  + (-1 / 512 : k) * b * f ^ 2

def quarticCostChamberBCDEFG2810_identityPartial1 (a b c d e f g : k) : k :=
  (207 / 917504 : k) * a ^ 3 * b ^ 6 * c * e + (207 / 917504 : k) * a ^ 3 * b ^ 5 * c ^ 2 * d
  + (381 / 65536 : k) * a ^ 3 * b ^ 5 * e * f + (927 / 57344 : k) * a ^ 3 * b ^ 4 * c * d * f
  + (-1583 / 57344 : k) * a ^ 3 * b ^ 3 * d * f ^ 2 + (-2325 / 458752 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e
  + (-1695 / 57344 : k) * a ^ 2 * b ^ 4 * c * e * g + (3597 / 458752 : k) * a ^ 2 * b ^ 3 * c ^ 4 * d
  + (5277 / 57344 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g
  + (-11397 / 114688 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (4929 / 14336 : k) * a ^ 2 * b ^ 3 * e * f * g
  + (-2105 / 16384 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d * f + (2635 / 14336 : k) * a ^ 2 * b ^ 2 * c * d * f * g
  + (237 / 1024 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2 + (299 / 448 : k) * a ^ 2 * b * c ^ 2 * d * f ^ 2
  + (-911 / 1792 : k) * a ^ 2 * b * d * f ^ 2 * g + (81 / 256 : k) * a ^ 2 * b * e * f ^ 3
  + (-331 / 448 : k) * a ^ 2 * c * d * f ^ 3 + (1737 / 114688 : k) * a * b ^ 2 * c ^ 5 * e
  + (-1245 / 14336 : k) * a * b ^ 2 * c ^ 3 * e * g + (-95 / 448 : k) * a * b ^ 2 * c * e * g ^ 2
  + (-2253 / 114688 : k) * a * b * c ^ 6 * d + (487 / 7168 : k) * a * b * c ^ 4 * d * g
  + (3405 / 14336 : k) * a * b * c ^ 4 * e * f + (817 / 1792 : k) * a * b * c ^ 2 * d * g ^ 2
  + (-2399 / 1792 : k) * a * b * c ^ 2 * e * f * g + (57 / 56 : k) * a * b * e * f * g ^ 2
  + (-297 / 28672 : k) * a * c ^ 5 * d * f + (75 / 1792 : k) * a * c ^ 3 * d * f * g
  + (-3405 / 3584 : k) * a * c ^ 3 * e * f ^ 2 + (43 / 64 : k) * a * c * d * f * g ^ 2
  + (757 / 448 : k) * a * c * e * f ^ 2 * g + (33 / 512 : k) * c ^ 5 * e * g
  + (-11 / 32 : k) * c ^ 3 * e * g ^ 2 + (11 / 8 : k) * c * e * g ^ 3

def quarticCostChamberBCDEFG2810_identityPartial2 (a b c d e f g : k) : k :=
  (-207 / 917504 : k) * a ^ 3 * b ^ 6 * c * e + (801 / 917504 : k) * a ^ 3 * b ^ 5 * c ^ 2 * d
  + (3 / 512 : k) * a ^ 3 * b ^ 5 * d * g + (-381 / 65536 : k) * a ^ 3 * b ^ 5 * e * f
  + (-591 / 57344 : k) * a ^ 3 * b ^ 4 * c * d * f + (1919 / 57344 : k) * a ^ 3 * b ^ 3 * d * f ^ 2
  + (-1707 / 458752 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (-993 / 57344 : k) * a ^ 2 * b ^ 4 * c * e * g
  + (-5613 / 458752 : k) * a ^ 2 * b ^ 3 * c ^ 4 * d + (-5949 / 57344 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g
  + (7365 / 114688 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (1 / 16 : k) * a ^ 2 * b ^ 3 * d * g ^ 2
  + (-4033 / 14336 : k) * a ^ 2 * b ^ 3 * e * f * g + (1721 / 16384 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d * f
  + (-1739 / 14336 : k) * a ^ 2 * b ^ 2 * c * d * f * g + (-221 / 1024 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2
  + (-619 / 896 : k) * a ^ 2 * b * c ^ 2 * d * f ^ 2 + (1023 / 1792 : k) * a ^ 2 * b * d * f ^ 2 * g
  + (-65 / 256 : k) * a ^ 2 * b * e * f ^ 3 + (331 / 448 : k) * a ^ 2 * c * d * f ^ 3
  + (-1737 / 114688 : k) * a * b ^ 2 * c ^ 5 * e + (1245 / 14336 : k) * a * b ^ 2 * c ^ 3 * e * g
  + (95 / 448 : k) * a * b ^ 2 * c * e * g ^ 2 + (2253 / 114688 : k) * a * b * c ^ 6 * d
  + (-487 / 7168 : k) * a * b * c ^ 4 * d * g + (-3405 / 14336 : k) * a * b * c ^ 4 * e * f
  + (975 / 1792 : k) * a * b * c ^ 2 * d * g ^ 2 + (2399 / 1792 : k) * a * b * c ^ 2 * e * f * g
  + (-57 / 56 : k) * a * b * e * f * g ^ 2 + (297 / 28672 : k) * a * c ^ 5 * d * f
  + (-75 / 1792 : k) * a * c ^ 3 * d * f * g + (3405 / 3584 : k) * a * c ^ 3 * e * f ^ 2
  + (-43 / 64 : k) * a * c * d * f * g ^ 2 + (-757 / 448 : k) * a * c * e * f ^ 2 * g
  + (-33 / 512 : k) * c ^ 5 * e * g + (11 / 32 : k) * c ^ 3 * e * g ^ 2 + (-11 / 8 : k) * c * e * g ^ 3

def quarticCostChamberBCDEFG2810_identityPartial3 (a b c d e f g : k) : k :=
  (-9 / 8192 : k) * a ^ 3 * b ^ 5 * c ^ 2 * d + (-3 / 512 : k) * a ^ 3 * b ^ 5 * d * g
  + (-3 / 512 : k) * a ^ 3 * b ^ 4 * c * d * f + (-3 / 512 : k) * a ^ 3 * b ^ 3 * d * f ^ 2
  + (9 / 1024 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e + (3 / 64 : k) * a ^ 2 * b ^ 4 * c * e * g
  + (9 / 2048 : k) * a ^ 2 * b ^ 3 * c ^ 4 * d + (3 / 256 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d * g
  + (9 / 256 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f + (-1 / 16 : k) * a ^ 2 * b ^ 3 * d * g ^ 2
  + (-1 / 16 : k) * a ^ 2 * b ^ 3 * e * f * g + (3 / 128 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d * f
  + (-1 / 16 : k) * a ^ 2 * b ^ 2 * c * d * f * g + (-1 / 64 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2
  + (3 / 128 : k) * a ^ 2 * b * c ^ 2 * d * f ^ 2 + (-1 / 16 : k) * a ^ 2 * b * d * f ^ 2 * g
  + (-1 / 16 : k) * a ^ 2 * b * e * f ^ 3

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #2: `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*d*g^2`, 43 cofactor terms. -/
theorem quarticCostChamberBCDEFG2810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG2Face810 a b c d e f g + xiQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG2Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG2Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG2Face810 a b c d e f g)) +
      (n4QuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * n4QuarticCostChamberBCDEFG2Face810 a b c d e f g)) =
      a * b * c ^ 2 * d * g ^ 2 := by
  have h1 : muQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG2Face810 a b c d e f g + xiQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG2Face810 a b c d e f g = quarticCostChamberBCDEFG2810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG2Cofactor810, muQuarticCostChamberBCDEFG2Face810, xiQuarticCostChamberBCDEFG2Cofactor810, xiQuarticCostChamberBCDEFG2Face810, quarticCostChamberBCDEFG2810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG2Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG2Face810 a b c d e f g = quarticCostChamberBCDEFG2810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG2Cofactor810, piQuarticCostChamberBCDEFG2Face810, kappaQuarticCostChamberBCDEFG2Cofactor810, kappaQuarticCostChamberBCDEFG2Face810, quarticCostChamberBCDEFG2810_identityPartial2]
    ring
  have h3 : n4QuarticCostChamberBCDEFG2Cofactor810 a b c d e f g * n4QuarticCostChamberBCDEFG2Face810 a b c d e f g = quarticCostChamberBCDEFG2810_identityPartial3 a b c d e f g := by
    simp only [n4QuarticCostChamberBCDEFG2Cofactor810, n4QuarticCostChamberBCDEFG2Face810, quarticCostChamberBCDEFG2810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG2810_identityPartial1, quarticCostChamberBCDEFG2810_identityPartial2, quarticCostChamberBCDEFG2810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG2810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (hn4 : n4QuarticCostChamberBCDEFG2Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG2810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn4] at hid
  have hz : a * b * c ^ 2 * d * g ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact (hd hRl).elim
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (306375 / 10621952 : k) * a ^ 2 * b ^ 2 * d ^ 2 + (-8489786204025 / 236733513191538688 : k) * a * b ^ 6
  + (24203652502940644395439437237 / 86501963629035729667428343808 : k) * a * b ^ 3 * c * d
  + (-86627058343584314136045208013 / 86501963629035729667428343808 : k) * a * b ^ 2 * d * f
  + (-41925 / 2655488 : k) * a * c ^ 2 * d ^ 2 + (102125 / 331936 : k) * a * d ^ 2 * g
  + (1818424565942034485326844391 / 1704472189734694180638982144 : k) * b ^ 4 * c ^ 2
  + (-57356709145669456587333265 / 168949147712960409506695984 : k) * b ^ 4 * g
  + (-104626839732757891739784367 / 24135592530422915643813712 : k) * b ^ 3 * c * f
  + (83918472870072414063667556095 / 21625490907258932416857085952 : k) * b ^ 2 * f ^ 2
  + (-6517147829218703765241 / 12672278815014380097536 : k) * b * c ^ 3 * d
  + (60104648120576522411393 / 36432801593166342780416 : k) * b * c * d * g
  + (1509161155411064241 / 1613482895744591872 : k) * c ^ 2 * d * f
  + (-3535662523195187727 / 311695559405205248 : k) * d * f * g

def xiQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 24 * a * b * c * d + (-32 : k) * a * d * f + 36 * b ^ 2 * c ^ 2
  + (-32 : k) * b ^ 2 * g + (-80 : k) * b * c * f + 64 * f ^ 2

def xiQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (71741522324055 / 236733513191538688 : k) * a * b ^ 4 * c
  + (-7304570789997530201916654721 / 216254909072589324168570859520 : k) * a * b ^ 3 * f
  + (-1075 / 230912 : k) * a * b * c ^ 2 * d + (-50525 / 663872 : k) * a * b * d * g
  + (-63425 / 1327744 : k) * a * c * d * f
  + (10161435150145635422189704895 / 43250981814517864833714171904 : k) * b ^ 2 * c ^ 3
  + (-5756361821531483068344382367 / 10812745453629466208428542976 : k) * b ^ 2 * c * g
  + (-85363223735078739635607699 / 93535860325514413567720960 : k) * b * c ^ 2 * f
  + (12662968548288402181 / 17143255767286288640 : k) * b * f * g
  + (12662968548288402181 / 17143255767286288640 : k) * c * f ^ 2

def piQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (-134758511175 / 13925500775972864 : k) * a * b ^ 3 * d + (-1075 / 129536 : k) * a * c * d ^ 2
  + (6827421669225 / 55702003103891456 : k) * b ^ 4 * c
  + (-95296593996145079 / 24662061874247942144 : k) * b ^ 3 * f
  + (-776567937635417 / 536131779874955264 : k) * b * c ^ 2 * d
  + (-29795570675430877 / 1541378867140496384 : k) * b * d * g
  + (-2058412336941 / 130741665646592 : k) * c * d * f

def kappaQuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (-404275533525 / 13925500775972864 : k) * a ^ 2 * b ^ 4 * d
  + (80625 / 1327744 : k) * a ^ 2 * b * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 2 * d ^ 2 * f
  + (37406699582145 / 72841080982011904 : k) * a * b ^ 5 * c
  + (-77674561570759903607185217187 / 865019636290357296674283438080 : k) * a * b ^ 4 * f
  + (119961310791003313144938941 / 172486467854507935528271872 : k) * a * b ^ 2 * c ^ 2 * d
  + (709924630645330306640845 / 1369595275155422342995968 : k) * a * b ^ 2 * d * g
  + (-338277241374667905607843859 / 165206194860648834353377280 : k) * a * b * c * d * f
  + (3035389292883998949 / 4285813941821572160 : k) * a * d * f ^ 2
  + (2202913219370688464780866053 / 4739833623508807105064566784 : k) * b ^ 3 * c ^ 3
  + (10104958976132890659839897 / 9978479861846648498970624 : k) * b ^ 3 * c * g
  + (-1303312252875391504269272559 / 620530585574144402205368320 : k) * b ^ 2 * c ^ 2 * f
  + (-1494851127721140434183 / 1234314415244612782080 : k) * b ^ 2 * f * g
  + (152547741673630055616892297 / 48926450016422924020038656 : k) * b * c * f ^ 2
  + (-22575 / 713728 : k) * c ^ 4 * d + (28936180369735246397 / 246862883048922556416 : k) * c ^ 2 * d * g
  + (33476795979037137983 / 5445504773137997568 : k) * d * g ^ 2
  + (-12662968548288402181 / 8571627883643144320 : k) * f ^ 3

def n2QuarticCostChamberBCDEFG3Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 7 * b ^ 3 * c + (-12 : k) * b ^ 2 * f + (-12 : k) * c ^ 2 * d + 32 * d * g

def n2QuarticCostChamberBCDEFG3Cofactor810 (a b c d e f g : k) : k :=
  (134758511175 / 6962750387986432 : k) * a ^ 2 * b ^ 5 + (-433225 / 10621952 : k) * a ^ 2 * b ^ 2 * c * d
  + (76325 / 663872 : k) * a ^ 2 * b * d * f
  + (-148217539479813251853480729 / 350920744945378213660966912 : k) * a * b ^ 3 * c ^ 2
  + (-15964966090082343775487 / 69640437719767237779456 : k) * a * b ^ 3 * g
  + (393184403423561718068756079 / 175460372472689106830483456 : k) * a * b ^ 2 * c * f
  + (-53411281163041567780899 / 19022156599380865874944 : k) * a * b * f ^ 2
  + (-3225 / 115456 : k) * a * c ^ 3 * d + (-13975 / 331936 : k) * a * c * d * g
  + (357111649996001035995 / 1810325545002054299648 : k) * b * c ^ 4
  + (-648744782492956030092913907 / 394785838063550490368587776 : k) * b * c ^ 2 * g
  + (-709924630645330306640845 / 128399557045820844655872 : k) * b * g ^ 2
  + (-12592848312077406207 / 27429209227658061824 : k) * c ^ 3 * f
  + (131906475228771548681 / 23143395285836489664 : k) * c * f * g

def quarticCostChamberBCDEFG3810_identityPartial1 (a b c d e f g : k) : k :=
  (919125 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-306375 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f
  + (-15043370349015 / 14795844574471168 : k) * a ^ 2 * b ^ 8 * c
  + (21975755396139435971852270913 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f
  + (398118802790466194565788913 / 462577345609816736189456384 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d
  + (151575 / 663872 : k) * a ^ 2 * b ^ 5 * d * g
  + (-20273364047907900355616031 / 3424653924961626126049280 : k) * a ^ 2 * b ^ 4 * c * d * f
  + (15207242368958553231 / 1672512757784028160 : k) * a ^ 2 * b ^ 3 * d * f ^ 2
  + (-364425 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2
  + (3225 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g
  + (-289175 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (-1075 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g
  + (63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2
  + (45651084107159531250336307461 / 18210939711375943087879651328 : k) * a * b ^ 6 * c ^ 3
  + (87142350193274227539 / 153477295770989425664 : k) * a * b ^ 6 * c * g
  + (-105712157500132227807472458537 / 5274509977380227418745630720 : k) * a * b ^ 5 * c ^ 2 * f
  + (21366563471104860432053675553 / 13515931817036832760535678720 : k) * a * b ^ 5 * f * g
  + (389482770919523749602714308541 / 8317496502791897083406571520 : k) * a * b ^ 4 * c * f ^ 2
  + (7146387902934472338125782377 / 2544175400853992049042010112 : k) * a * b ^ 3 * c ^ 4 * d
  + (-66545120632391553582681257 / 45431703586678429447178752 : k) * a * b ^ 3 * c ^ 2 * d * g
  + (50525 / 20746 : k) * a * b ^ 3 * d * g ^ 2
  + (-81322818830239985319 / 2449036538183755520 : k) * a * b ^ 3 * f ^ 3
  + (-5736622049976496092151038979 / 289110841006135460118410240 : k) * a * b ^ 2 * c ^ 3 * d * f
  + (-9480398995258144761969591 / 256966649245918718592640 : k) * a * b ^ 2 * c * d * f * g
  + (34165560315753049348025344349 / 795054812766872515325628160 : k) * a * b * c ^ 2 * d * f ^ 2
  + (133371853726969312261 / 2142906970910786080 : k) * a * b * d * f ^ 2 * g
  + (41925 / 663872 : k) * a * c ^ 5 * d ^ 2 + (-72025 / 41492 : k) * a * c ^ 3 * d ^ 2 * g
  + (102125 / 10373 : k) * a * c * d ^ 2 * g ^ 2
  + (-1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3
  + (362483143924252749876309341067 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5
  + (95302997651225907569791322841 / 10812745453629466208428542976 : k) * b ^ 4 * c ^ 3 * g
  + (29602276306665925073 / 4796165492843419552 : k) * b ^ 4 * c * g ^ 2
  + (-66247321088877544520293841499 / 1930847402433833251505096960 : k) * b ^ 3 * c ^ 4 * f
  + (-4466366059525506282488141 / 110735496960713383697120 : k) * b ^ 3 * c ^ 2 * f * g
  + (-12662968548288402181 / 535726742727696520 : k) * b ^ 3 * f * g ^ 2
  + (22514989088246482852509668739 / 227158517933392147235893760 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (34095289019550827906752641 / 4622411702132979740265280 : k) * b ^ 2 * c * f ^ 2 * g
  + (6517147829218703765241 / 3168069703753595024384 : k) * b * c ^ 6 * d
  + (-6562470256018959656623 / 284631262446612052972 : k) * b * c ^ 4 * d * g
  + (60104648120576522411393 / 1138525049786448211888 : k) * b * c ^ 2 * d * g ^ 2
  + (-5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3
  + (12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g
  + (-1509161155411064241 / 403370723936147968 : k) * c ^ 5 * d * f
  + (32274013698567578547 / 428581394182157216 : k) * c ^ 3 * d * f * g
  + (-3535662523195187727 / 9740486231412664 : k) * c * d * f * g ^ 2
  + (12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

def quarticCostChamberBCDEFG3810_identityPartial2 (a b c d e f g : k) : k :=
  (-404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d
  + (190275 / 5310976 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f
  + (104310699962295 / 118366756595769344 : k) * a ^ 2 * b ^ 8 * c
  + (-21925530089258656389769451163 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f
  + (7044131506046122708369531537 / 10176701603415968196168040448 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d
  + (628379294481695956874533 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g
  + (-3810822752374450789365119719 / 1817268143467137177887150080 : k) * a ^ 2 * b ^ 4 * c * d * f
  + (1056202824840943267347 / 1486105984326630146480 : k) * a ^ 2 * b ^ 3 * d * f ^ 2
  + (-87075 / 663872 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2
  + (117175 / 82984 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g
  + (747125 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f
  + (-151575 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g + (-63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2
  + (155626859453639970536334149799 / 346007854516142918669713375232 : k) * a * b ^ 6 * c ^ 3
  + (10347213948186673629137837 / 9978479861846648498970624 : k) * a * b ^ 6 * c * g
  + (-44019624995593251425232075003 / 61787116877882664048163102720 : k) * a * b ^ 5 * c ^ 2 * f
  + (-4215502734257277845144973117101 / 973147090826651958758568867840 : k) * a * b ^ 5 * f * g
  + (-661758235232847097126742823 / 2350596837745536132267074560 : k) * a * b ^ 4 * c * f ^ 2
  + (-513401819752361576574050265 / 62053058557414440220536832 : k) * a * b ^ 3 * c ^ 4 * d
  + (49956985392305014269906269557 / 2862197325960741055172261376 : k) * a * b ^ 3 * c ^ 2 * d * g
  + (689750356046346517189867 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2
  + (-5802984711411749625657 / 11888847874613041171840 : k) * a * b ^ 3 * f ^ 3
  + (151934614432978587766505530199 / 3180219251067490061302512640 : k) * a * b ^ 2 * c ^ 3 * d * f
  + (-5138060070301936480675711793 / 98020456368518529286721280 : k) * a * b ^ 2 * c * d * f * g
  + (-30079600313357745180524257067 / 397527406383436257662814080 : k) * a * b * c ^ 2 * d * f ^ 2
  + (446030677695116319557 / 16153325916593805940 : k) * a * b * d * f ^ 2 * g
  + (-3225 / 8096 : k) * a * c ^ 5 * d ^ 2 + (1075 / 506 : k) * a * c ^ 3 * d ^ 2 * g
  + (-2150 / 253 : k) * a * c * d ^ 2 * g ^ 2
  + (1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3
  + (-481929070825741485105660543957 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5
  + (47578571514647720326763825629 / 17693583469575490159246706688 : k) * b ^ 4 * c ^ 3 * g
  + (10144097124616423428348197 / 311827495682707765592832 : k) * b ^ 4 * c * g ^ 2
  + (616185350475785252973327994947 / 15446779219470666012040775680 : k) * b ^ 3 * c ^ 4 * f
  + (-14073502449611371011668000966051 / 729860318119988969068926650880 : k) * b ^ 3 * c ^ 2 * f * g
  + (-175772958624644502907757 / 4115370418135283482560 : k) * b ^ 3 * f * g ^ 2
  + (-1808317652048889402615960279 / 17283800277540706854904960 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (109153969120539636339947328713 / 1788873328725463159482663360 : k) * b ^ 2 * c * f ^ 2 * g
  + (425930971681404159 / 1373837685929572864 : k) * b * c ^ 6 * d
  + (-4994646827546302311415 / 1678425582298311694848 : k) * b * c ^ 4 * d * g
  + (-356067772626052476285271 / 5349981543575868527328 : k) * b * c ^ 2 * d * g ^ 2
  + (5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3
  + (709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3
  + (-12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g
  + (-10068775161332331 / 5695433809729664 : k) * c ^ 5 * d * f
  + (60029289149566436741 / 7714465095278829888 : k) * c ^ 3 * d * f * g
  + (30733286380816738835 / 170172024160562424 : k) * c * d * f * g ^ 2
  + (-12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

def quarticCostChamberBCDEFG3810_identityPartial3 (a b c d e f g : k) : k :=
  (404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d
  + (-1299675 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2
  + (228975 / 663872 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f
  + (943309578225 / 6962750387986432 : k) * a ^ 2 * b ^ 8 * c
  + (-404275533525 / 1740687596996608 : k) * a ^ 2 * b ^ 7 * f
  + (-544922247152978585821271987 / 350920744945378213660966912 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d
  + (-941084761547159090791333 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g
  + (1406636827897586915813677037 / 175460372472689106830483456 : k) * a ^ 2 * b ^ 4 * c * d * f
  + (-186477446517077283139497 / 19022156599380865874944 : k) * a ^ 2 * b ^ 3 * d * f ^ 2
  + (538575 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2
  + (-237575 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g
  + (-228975 / 165968 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (76325 / 20746 : k) * a ^ 2 * b * d ^ 2 * f * g
  + (-148217539479813251853480729 / 50131534992196887665852416 : k) * a * b ^ 6 * c ^ 3
  + (-15964966090082343775487 / 9948633959966748254208 : k) * a * b ^ 6 * c * g
  + (3641596060843811537602176927 / 175460372472689106830483456 : k) * a * b ^ 5 * c ^ 2 * f
  + (15964966090082343775487 / 5803369809980603148288 : k) * a * b ^ 5 * f * g
  + (-2041718110804502141325539895 / 43865093118172276707620864 : k) * a * b ^ 4 * c * f ^ 2
  + (59927097874622208195733959 / 10966273279543069176905216 : k) * a * b ^ 3 * c ^ 4 * d
  + (-789045565387316317141333627 / 49348229757943811296073472 : k) * a * b ^ 3 * c ^ 2 * d * g
  + (-767926722812712300669067 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2
  + (160233843489124703342697 / 4755539149845216468736 : k) * a * b ^ 3 * f ^ 3
  + (-1902586675588715586910347 / 68113498630702293024256 : k) * a * b ^ 2 * c ^ 3 * d * f
  + (4407376383131032152628497875 / 49348229757943811296073472 : k) * a * b ^ 2 * c * d * f * g
  + (160233843489124703342697 / 4755539149845216468736 : k) * a * b * c ^ 2 * d * f ^ 2
  + (-53411281163041567780899 / 594442393730652058592 : k) * a * b * d * f ^ 2 * g
  + (9675 / 28864 : k) * a * c ^ 5 * d ^ 2 + (-16125 / 41492 : k) * a * c ^ 3 * d ^ 2 * g
  + (-13975 / 10373 : k) * a * c * d ^ 2 * g ^ 2
  + (2499781549972007251965 / 1810325545002054299648 : k) * b ^ 4 * c ^ 5
  + (-648744782492956030092913907 / 56397976866221498624083968 : k) * b ^ 4 * c ^ 3 * g
  + (-709924630645330306640845 / 18342793863688692093696 : k) * b ^ 4 * c * g ^ 2
  + (-34972325259539511890862987 / 6266441874024610958231552 : k) * b ^ 3 * c ^ 4 * f
  + (1357822697479463614657454143 / 22776106042127912905880064 : k) * b ^ 3 * c ^ 2 * f * g
  + (709924630645330306640845 / 10699963087151737054656 : k) * b ^ 3 * f * g ^ 2
  + (37778544936232218621 / 6857302306914515456 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (-131906475228771548681 / 1928616273819707472 : k) * b ^ 2 * c * f ^ 2 * g
  + (-1071334949988003107985 / 452581386250513574912 : k) * b * c ^ 6 * d
  + (856416634538430504557158247 / 32898819838629207530715648 : k) * b * c ^ 4 * d * g
  + (84899158320554906731990189 / 6168528719742976412009184 : k) * b * c ^ 2 * d * g ^ 2
  + (-709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3
  + (37778544936232218621 / 6857302306914515456 : k) * c ^ 5 * d * f
  + (-640961535723782850587 / 7714465095278829888 : k) * c ^ 3 * d * f * g
  + (131906475228771548681 / 723231102682390302 : k) * c * d * f * g ^ 2

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #3: `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*d*f^2`, 63 cofactor terms. -/
theorem quarticCostChamberBCDEFG3810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG3Face810 a b c d e f g + xiQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG3Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG3Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG3Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG3Face810 a b c d e f g)) =
      a * b * c ^ 2 * d * f ^ 2 := by
  have h1 : muQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG3Face810 a b c d e f g + xiQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG3Face810 a b c d e f g = quarticCostChamberBCDEFG3810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG3Cofactor810, muQuarticCostChamberBCDEFG3Face810, xiQuarticCostChamberBCDEFG3Cofactor810, xiQuarticCostChamberBCDEFG3Face810, quarticCostChamberBCDEFG3810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG3Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG3Face810 a b c d e f g = quarticCostChamberBCDEFG3810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG3Cofactor810, piQuarticCostChamberBCDEFG3Face810, kappaQuarticCostChamberBCDEFG3Cofactor810, kappaQuarticCostChamberBCDEFG3Face810, quarticCostChamberBCDEFG3810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG3Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG3Face810 a b c d e f g = quarticCostChamberBCDEFG3810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG3Cofactor810, n2QuarticCostChamberBCDEFG3Face810, quarticCostChamberBCDEFG3810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG3810_identityPartial1, quarticCostChamberBCDEFG3810_identityPartial2, quarticCostChamberBCDEFG3810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG3810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG3Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG3810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c ^ 2 * d * f ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (19327 / 678912 : k) * a * b ^ 4 * e + (553 / 3328 : k) * a * b ^ 2 * e ^ 2 + (35 / 2048 : k) * b ^ 4 * g
  + (-11741171 / 88833024 : k) * b ^ 3 * c * f + (-312863 / 1584128 : k) * b ^ 2 * c ^ 2 * e
  + (7657 / 4352 : k) * b ^ 2 * e * g + (223531 / 2115072 : k) * b ^ 2 * f ^ 2
  + (37859449 / 24058944 : k) * b * c * e * f + (-291 / 208 : k) * c ^ 2 * e ^ 2 + (74 / 39 : k) * e ^ 2 * g
  + (866251 / 1288872 : k) * e * f ^ 2

def xiQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 12 * a * b ^ 2 * e + 36 * b ^ 2 * c ^ 2 + (-32 : k) * b ^ 2 * g
  + (-80 : k) * b * c * f + (-48 : k) * c ^ 2 * e + 128 * e * g + 64 * f ^ 2

def xiQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (1985773 / 157925376 : k) * a * b ^ 3 * f + (-1023 / 23296 : k) * a * b ^ 2 * c * e
  + (7531 / 104832 : k) * a * b * e * f + (281 / 4608 : k) * b ^ 2 * c * g
  + (-172531 / 1880064 : k) * b * c ^ 2 * f + (7495 / 705024 : k) * b * f * g + (217 / 1248 : k) * c ^ 3 * e
  + (-97 / 104 : k) * c * e * g + (7495 / 705024 : k) * c * f ^ 2

def piQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (667 / 86016 : k) * b ^ 3 * f + (-1375 / 86016 : k) * b ^ 2 * c * e + (-131 / 5376 : k) * b * e * f
  + (11 / 192 : k) * c * e ^ 2

def kappaQuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (761161 / 52641792 : k) * a * b ^ 4 * f + (-551023 / 19009536 : k) * a * b ^ 3 * c * e
  + (21407735 / 171085824 : k) * a * b ^ 2 * e * f + (-2077 / 3328 : k) * a * b * c * e ^ 2
  + (461 / 416 : k) * a * e ^ 2 * f + (713615 / 2506752 : k) * b ^ 3 * c * g
  + (-41495 / 626688 : k) * b ^ 2 * c ^ 2 * f + (-25674133 / 39481344 : k) * b ^ 2 * f * g
  + (29619 / 56576 : k) * b * c ^ 3 * e + (-92673097 / 28514304 : k) * b * c * e * g
  + (285029 / 1410048 : k) * b * c * f ^ 2 + (-224453 / 470016 : k) * c ^ 2 * e * f
  + (9070715 / 4935168 : k) * e * f * g + (-7495 / 352512 : k) * f ^ 3

def n2QuarticCostChamberBCDEFG4Face810 (a b c d e f g : k) : k :=
  7 * b ^ 3 * c + (-12 : k) * b ^ 2 * f + (-24 : k) * b * c * e + 32 * e * f

def n2QuarticCostChamberBCDEFG4Cofactor810 (a b c d e f g : k) : k :=
  (-5599 / 279552 : k) * a ^ 2 * b ^ 3 * e + (-383543 / 17547264 : k) * a * b ^ 3 * g
  + (1973693 / 29611008 : k) * a * b ^ 2 * c * f + (7853 / 69888 : k) * a * b * c ^ 2 * e
  + (-12071 / 13104 : k) * a * b * e * g + (-947143 / 5552064 : k) * a * b * f ^ 2
  + (-811 / 1248 : k) * a * c * e * f + (269303 / 1462272 : k) * b * c ^ 2 * g
  + (-201197 / 182784 : k) * b * g ^ 2 + (728893 / 3172608 : k) * c ^ 3 * f
  + (-30523639 / 44416512 : k) * c * f * g

def quarticCostChamberBCDEFG4810_identityPartial1 (a b c d e f g : k) : k :=
  (-1985773 / 52641792 : k) * a ^ 2 * b ^ 7 * f + (343981 / 1584128 : k) * a ^ 2 * b ^ 6 * c * e
  + (-50019959 / 171085824 : k) * a ^ 2 * b ^ 5 * e * f + (-51 / 1792 : k) * a ^ 2 * b ^ 4 * c * e ^ 2
  + (-157 / 336 : k) * a ^ 2 * b ^ 3 * e ^ 2 * f + (-809 / 6144 : k) * a * b ^ 6 * c * g
  + (19629773 / 59222016 : k) * a * b ^ 5 * c ^ 2 * f + (-1408949 / 2467584 : k) * a * b ^ 5 * f * g
  + (-13348843 / 4752384 : k) * a * b ^ 4 * c ^ 3 * e + (13216729 / 1188096 : k) * a * b ^ 4 * c * e * g
  + (29901379 / 88833024 : k) * a * b ^ 4 * c * f ^ 2
  + (343089769 / 32078592 : k) * a * b ^ 3 * c ^ 2 * e * f
  + (-58692395 / 4009824 : k) * a * b ^ 3 * e * f * g + (-301549 / 7402752 : k) * a * b ^ 3 * f ^ 3
  + (-299 / 448 : k) * a * b ^ 2 * c ^ 3 * e ^ 2 + (-325 / 56 : k) * a * b ^ 2 * c * e ^ 2 * g
  + (-304787801 / 16039296 : k) * a * b ^ 2 * c * e * f ^ 2 + (1301 / 168 : k) * a * b * c ^ 2 * e ^ 2 * f
  + (-377 / 63 : k) * a * b * e ^ 2 * f * g + (-135179 / 173502 : k) * a * b * e * f ^ 3
  + (1089 / 512 : k) * b ^ 4 * c ^ 3 * g + (-809 / 576 : k) * b ^ 4 * c * g ^ 2
  + (-246510547 / 88833024 : k) * b ^ 3 * c ^ 4 * f + (-4017365 / 694008 : k) * b ^ 3 * c ^ 2 * f * g
  + (-7495 / 22032 : k) * b ^ 3 * f * g ^ 2 + (2791871 / 396032 : k) * b ^ 2 * c ^ 5 * e
  + (-16462777 / 297024 : k) * b ^ 2 * c ^ 3 * e * g + (7721563 / 1057536 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (1494983 / 15912 : k) * b ^ 2 * c * e * g ^ 2 + (805583 / 132192 : k) * b ^ 2 * c * f ^ 2 * g
  + (-1520506837 / 96235776 : k) * b * c ^ 4 * e * f + (677946785 / 6014736 : k) * b * c ^ 2 * e * f * g
  + (-592543 / 88128 : k) * b * c ^ 2 * f ^ 3 + (7495 / 5508 : k) * b * e * f * g ^ 2
  + (7495 / 11016 : k) * b * f ^ 3 * g + (-11 / 4 : k) * c ^ 5 * e ^ 2 + (44 / 3 : k) * c ^ 3 * e ^ 2 * g
  + (3144659 / 396576 : k) * c ^ 3 * e * f ^ 2 + (-176 / 3 : k) * c * e ^ 2 * g ^ 2
  + (-1825457 / 49572 : k) * c * e * f ^ 2 * g + (7495 / 11016 : k) * c * f ^ 4

def quarticCostChamberBCDEFG4810_identityPartial2 (a b c d e f g : k) : k :=
  (1985773 / 52641792 : k) * a ^ 2 * b ^ 7 * f + (-182831 / 2376192 : k) * a ^ 2 * b ^ 6 * c * e
  + (8900903 / 171085824 : k) * a ^ 2 * b ^ 5 * e * f + (-1505 / 3328 : k) * a ^ 2 * b ^ 4 * c * e ^ 2
  + (461 / 416 : k) * a ^ 2 * b ^ 3 * e ^ 2 * f + (713615 / 2506752 : k) * a * b ^ 6 * c * g
  + (-583475 / 731136 : k) * a * b ^ 5 * c ^ 2 * f + (12187523 / 39481344 : k) * a * b ^ 5 * f * g
  + (3203605 / 1584128 : k) * a * b ^ 4 * c ^ 3 * e + (-148294201 / 28514304 : k) * a * b ^ 4 * c * e * g
  + (16359065 / 9870336 : k) * a * b ^ 4 * c * f ^ 2
  + (-34199273 / 10692864 : k) * a * b ^ 3 * c ^ 2 * e * f
  + (274757459 / 64157184 : k) * a * b ^ 3 * e * f * g + (-4950913 / 2467584 : k) * a * b ^ 3 * f ^ 3
  + (2799 / 832 : k) * a * b ^ 2 * c ^ 3 * e ^ 2 + (-5087 / 312 : k) * a * b ^ 2 * c * e ^ 2 * g
  + (26610959 / 5346432 : k) * a * b ^ 2 * c * e * f ^ 2 + (-2023 / 78 : k) * a * b * c ^ 2 * e ^ 2 * f
  + (461 / 13 : k) * a * b * e ^ 2 * f * g + (131 / 21 : k) * a * b * e * f ^ 3
  + (811 / 39 : k) * a * c * e ^ 2 * f ^ 2 + (-713615 / 208896 : k) * b ^ 4 * c ^ 3 * g
  + (713615 / 78336 : k) * b ^ 4 * c * g ^ 2 + (426533 / 365568 : k) * b ^ 3 * c ^ 4 * f
  + (42143539 / 3290112 : k) * b ^ 3 * c ^ 2 * f * g + (-15877237 / 1233792 : k) * b ^ 3 * f * g ^ 2
  + (-2791871 / 396032 : k) * b ^ 2 * c ^ 5 * e + (142205033 / 2376192 : k) * b ^ 2 * c ^ 3 * e * g
  + (-533999 / 117504 : k) * b ^ 2 * c ^ 3 * f ^ 2 + (-107259097 / 891072 : k) * b ^ 2 * c * e * g ^ 2
  + (-17693321 / 1233792 : k) * b ^ 2 * c * f ^ 2 * g + (75968183 / 3564288 : k) * b * c ^ 4 * e * f
  + (-722307217 / 5346432 : k) * b * c ^ 2 * e * f * g + (592543 / 88128 : k) * b * c ^ 2 * f ^ 3
  + (5222459 / 154224 : k) * b * e * f * g ^ 2 + (-7495 / 11016 : k) * b * f ^ 3 * g
  + (11 / 4 : k) * c ^ 5 * e ^ 2 + (-44 / 3 : k) * c ^ 3 * e ^ 2 * g
  + (-224453 / 14688 : k) * c ^ 3 * e * f ^ 2 + (176 / 3 : k) * c * e ^ 2 * g ^ 2
  + (9070715 / 154224 : k) * c * e * f ^ 2 * g + (-7495 / 11016 : k) * c * f ^ 4

def quarticCostChamberBCDEFG4810_identityPartial3 (a b c d e f g : k) : k :=
  (-5599 / 39936 : k) * a ^ 2 * b ^ 6 * c * e + (5599 / 23296 : k) * a ^ 2 * b ^ 5 * e * f
  + (5599 / 11648 : k) * a ^ 2 * b ^ 4 * c * e ^ 2 + (-5599 / 8736 : k) * a ^ 2 * b ^ 3 * e ^ 2 * f
  + (-383543 / 2506752 : k) * a * b ^ 6 * c * g + (1973693 / 4230144 : k) * a * b ^ 5 * c ^ 2 * f
  + (383543 / 1462272 : k) * a * b ^ 5 * f * g + (7853 / 9984 : k) * a * b ^ 4 * c ^ 3 * e
  + (-168907295 / 28514304 : k) * a * b ^ 4 * c * e * g + (-44283241 / 22208256 : k) * a * b ^ 4 * c * f ^ 2
  + (-120245975 / 16039296 : k) * a * b ^ 3 * c ^ 2 * e * f
  + (73813429 / 7128576 : k) * a * b ^ 3 * e * f * g + (947143 / 462672 : k) * a * b ^ 3 * f ^ 3
  + (-7853 / 2912 : k) * a * b ^ 2 * c ^ 3 * e ^ 2 + (12071 / 546 : k) * a * b ^ 2 * c * e ^ 2 * g
  + (56238731 / 4009824 : k) * a * b ^ 2 * c * e * f ^ 2 + (41915 / 2184 : k) * a * b * c ^ 2 * e ^ 2 * f
  + (-24142 / 819 : k) * a * b * e ^ 2 * f * g + (-947143 / 173502 : k) * a * b * e * f ^ 3
  + (-811 / 39 : k) * a * c * e ^ 2 * f ^ 2 + (269303 / 208896 : k) * b ^ 4 * c ^ 3 * g
  + (-201197 / 26112 : k) * b ^ 4 * c * g ^ 2 + (5102251 / 3172608 : k) * b ^ 3 * c ^ 4 * f
  + (-623652833 / 88833024 : k) * b ^ 3 * c ^ 2 * f * g + (201197 / 15232 : k) * b ^ 3 * f * g ^ 2
  + (-269303 / 60928 : k) * b ^ 2 * c ^ 3 * e * g + (-728893 / 264384 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (201197 / 7616 : k) * b ^ 2 * c * e * g ^ 2 + (30523639 / 3701376 : k) * b ^ 2 * c * f ^ 2 * g
  + (-728893 / 132192 : k) * b * c ^ 4 * e * f + (82860821 / 3701376 : k) * b * c ^ 2 * e * f * g
  + (-201197 / 5712 : k) * b * e * f * g ^ 2 + (728893 / 99144 : k) * c ^ 3 * e * f ^ 2
  + (-30523639 / 1388016 : k) * c * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #4: `BCDEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*e^2*f`, 49 cofactor terms. -/
theorem quarticCostChamberBCDEFG4810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG4Face810 a b c d e f g + xiQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG4Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG4Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG4Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG4Face810 a b c d e f g)) =
      a * b * c ^ 2 * e ^ 2 * f := by
  have h1 : muQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG4Face810 a b c d e f g + xiQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG4Face810 a b c d e f g = quarticCostChamberBCDEFG4810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG4Cofactor810, muQuarticCostChamberBCDEFG4Face810, xiQuarticCostChamberBCDEFG4Cofactor810, xiQuarticCostChamberBCDEFG4Face810, quarticCostChamberBCDEFG4810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG4Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG4Face810 a b c d e f g = quarticCostChamberBCDEFG4810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG4Cofactor810, piQuarticCostChamberBCDEFG4Face810, kappaQuarticCostChamberBCDEFG4Cofactor810, kappaQuarticCostChamberBCDEFG4Face810, quarticCostChamberBCDEFG4810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG4Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG4Face810 a b c d e f g = quarticCostChamberBCDEFG4810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG4Cofactor810, n2QuarticCostChamberBCDEFG4Face810, quarticCostChamberBCDEFG4810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG4810_identityPartial1, quarticCostChamberBCDEFG4810_identityPartial2, quarticCostChamberBCDEFG4810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG4810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG4Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG4810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c ^ 2 * e ^ 2 * f = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact he ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRl)
  ·
    exact (hf hR).elim

def muQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 44 : k) * c * d

def xiQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a * b * c * d + (-4 : k) * a * d * f

def xiQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (2 / 11 : k) * b * c + (-4 / 11 : k) * f

def piQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (1 / 176 : k) * d

def kappaQuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * a * b * d

def n2QuarticCostChamberBCDEFG5Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-12 : k) * c ^ 2 * d + 32 * d * g

def n2QuarticCostChamberBCDEFG5Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 88 : k) * a * b ^ 2 + (1 / 22 : k) * c ^ 2 + (-2 / 11 : k) * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #5: `BCDEFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC`, target `a*c*d^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCDEFG5810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG5Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG5Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG5Face810 a b c d e f g =
      a * c * d ^ 3 := by
  simp only [muQuarticCostChamberBCDEFG5Face810, xiQuarticCostChamberBCDEFG5Face810, piQuarticCostChamberBCDEFG5Face810, kappaQuarticCostChamberBCDEFG5Face810, n2QuarticCostChamberBCDEFG5Face810, muQuarticCostChamberBCDEFG5Cofactor810, xiQuarticCostChamberBCDEFG5Cofactor810, piQuarticCostChamberBCDEFG5Cofactor810, kappaQuarticCostChamberBCDEFG5Cofactor810, n2QuarticCostChamberBCDEFG5Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG5810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG5Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG5810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * c * d ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hc hRl).elim
  ·
    exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def xiQuarticCostChamberBCDEFG6Face810 (a b c d e f g : k) : k :=
  -a * d * f + 4 * e * g

def xiQuarticCostChamberBCDEFG6Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 2 : k) * f

def piQuarticCostChamberBCDEFG6Face810 (a b c d e f g : k) : k :=
  -a * f ^ 2 + 4 * g ^ 2

def piQuarticCostChamberBCDEFG6Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 2 : k) * d

def n2QuarticCostChamberBCDEFG6Face810 (a b c d e f g : k) : k :=
  d * g + e * f

def n2QuarticCostChamberBCDEFG6Cofactor810 (a b c d e f g : k) : k :=
  2 * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #6: `BCDEFG` / `BF·BG·CF·CG·DD·DE·EE`, target `a*d*f^2`, 3 cofactor terms. -/
theorem quarticCostChamberBCDEFG6810_identity
    (a b c d e f g : k) :
    xiQuarticCostChamberBCDEFG6Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG6Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG6Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG6Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG6Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG6Face810 a b c d e f g =
      a * d * f ^ 2 := by
  simp only [xiQuarticCostChamberBCDEFG6Face810, piQuarticCostChamberBCDEFG6Face810, n2QuarticCostChamberBCDEFG6Face810, xiQuarticCostChamberBCDEFG6Cofactor810, piQuarticCostChamberBCDEFG6Cofactor810, n2QuarticCostChamberBCDEFG6Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG6810_impossible
    (a b c d e f g : k)
    (hxi : xiQuarticCostChamberBCDEFG6Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG6Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG6Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG6810_identity a b c d e f g
  rw [hxi, hpi, hn2] at hid
  have hz : a * d * f ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

def muQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * c * e

def xiQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-12 : k) * c ^ 2 * e + 32 * e * g

def xiQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (1 / 352 : k) * a * b ^ 2 + (-1 / 88 : k) * c ^ 2 + (1 / 22 : k) * g

def piQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 704 : k) * e

def kappaQuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 704 : k) * a * b * e

def n2QuarticCostChamberBCDEFG7Face810 (a b c d e f g : k) : k :=
  (-3 : k) * b * c * e + 4 * e * f

def n2QuarticCostChamberBCDEFG7Cofactor810 (a b c d e f g : k) : k :=
  (1 / 22 : k) * a * b * c + (-1 / 11 : k) * a * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #7: `BCDEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC`, target `c*e^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCDEFG7810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG7Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG7Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG7Face810 a b c d e f g =
      c * e ^ 3 := by
  simp only [muQuarticCostChamberBCDEFG7Face810, xiQuarticCostChamberBCDEFG7Face810, piQuarticCostChamberBCDEFG7Face810, kappaQuarticCostChamberBCDEFG7Face810, n2QuarticCostChamberBCDEFG7Face810, muQuarticCostChamberBCDEFG7Cofactor810, xiQuarticCostChamberBCDEFG7Cofactor810, piQuarticCostChamberBCDEFG7Cofactor810, kappaQuarticCostChamberBCDEFG7Cofactor810, n2QuarticCostChamberBCDEFG7Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG7810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG7Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG7810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : c * e ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    exact (hc hL).elim
  ·
    exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * b * f - a * d ^ 2 + 4 * e ^ 2

def muQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (1 / 256 : k) * a * b ^ 4 + (1 / 24 : k) * b ^ 2 * g + (-1 / 3 : k) * f ^ 2

def xiQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-8 : k) * a * d * f + 32 * e * g

def xiQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 192 : k) * b ^ 2 * e + (1 / 24 : k) * d * f

def piQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + 64 * a * b ^ 2 * g + 256 * a * b * d * e + (-256 : k) * a * f ^ 2 + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (1 / 384 : k) * b * f

def kappaQuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + 32 * b * g + 32 * d * e

def kappaQuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 12 : k) * f * g

def n2QuarticCostChamberBCDEFG8Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 32 * d * g + 32 * e * f

def n2QuarticCostChamberBCDEFG8Cofactor810 (a b c d e f g : k) : k :=
  (1 / 768 : k) * a * b ^ 2 * d + (1 / 24 : k) * e * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #8: `BCDEFG` / `BF·BG·DD·DE·EE·BBB`, target `a*b^2*d*e*f`, 9 cofactor terms. -/
theorem quarticCostChamberBCDEFG8810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG8Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG8Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG8Face810 a b c d e f g =
      a * b ^ 2 * d * e * f := by
  simp only [muQuarticCostChamberBCDEFG8Face810, xiQuarticCostChamberBCDEFG8Face810, piQuarticCostChamberBCDEFG8Face810, kappaQuarticCostChamberBCDEFG8Face810, n2QuarticCostChamberBCDEFG8Face810, muQuarticCostChamberBCDEFG8Cofactor810, xiQuarticCostChamberBCDEFG8Cofactor810, piQuarticCostChamberBCDEFG8Cofactor810, kappaQuarticCostChamberBCDEFG8Cofactor810, n2QuarticCostChamberBCDEFG8Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG8810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG8Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG8810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b ^ 2 * d * e * f = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRlll)
      ·
        exact (hd hRll).elim
    ·
      exact (he hRl).elim
  ·
    exact (hf hR).elim

def muQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 16 * e ^ 2

def muQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 3410 : k) * b ^ 2 * c * e * f + (-9 / 1364 : k) * b ^ 2 * d * e ^ 2
  + (-681 / 13640 : k) * b * c ^ 2 * d * f + (-27 / 1705 : k) * b * c * d ^ 2 * e
  + (-16 / 1705 : k) * b * e * f ^ 2 + (-9 / 1705 : k) * c ^ 2 * d ^ 3 + (1143 / 27280 : k) * c * d * f ^ 2
  + (3369 / 54560 : k) * d ^ 2 * e * f

def xiQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e

def xiQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 2728 : k) * b ^ 3 * e ^ 2 + (1059 / 109120 : k) * b ^ 2 * c ^ 2 * f
  + (3 / 682 : k) * b ^ 2 * c * d * e + (9 / 2728 : k) * b * c ^ 2 * d ^ 2
  + (-549 / 13640 : k) * b * c * f ^ 2 + (-189 / 109120 : k) * b * d * e * f
  + (131 / 109120 : k) * c * d ^ 2 * f + (-3 / 682 : k) * d ^ 3 * e + (131 / 6820 : k) * f ^ 3

def piQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 128 * a * b * c * f + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-512 : k) * c * e ^ 2

def piQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * b ^ 2 * e * f + (-741 / 436480 : k) * b * c * d * f + (-27 / 54560 : k) * b * d ^ 2 * e
  + (-9 / 54560 : k) * c * d ^ 3 + (-131 / 218240 : k) * d * f ^ 2

def kappaQuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * c * f + 32 * d * e

def kappaQuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (9 / 27280 : k) * a * b ^ 3 * e * f + (435 / 87296 : k) * a * b ^ 2 * c * d * f
  + (27 / 6820 : k) * a * b ^ 2 * d ^ 2 * e + (117 / 54560 : k) * a * b * c * d ^ 3
  + (921 / 54560 : k) * a * b * d * f ^ 2 + (2889 / 436480 : k) * a * d ^ 3 * f
  + (9 / 2728 : k) * b ^ 2 * e ^ 3 + (-645 / 21824 : k) * b * c ^ 2 * e * f
  + (-9 / 2728 : k) * b * c * d * e ^ 2 + (-9 / 2728 : k) * c ^ 2 * d ^ 2 * e
  + (643 / 27280 : k) * c * e * f ^ 2 + (-2889 / 109120 : k) * d * e ^ 2 * f

def n2QuarticCostChamberBCDEFG9Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * e * f

def n2QuarticCostChamberBCDEFG9Cofactor810 (a b c d e f g : k) : k :=
  (1 / 27280 : k) * a * b ^ 3 * c * f + (-9 / 10912 : k) * a * b ^ 3 * d * e
  + (-3 / 5456 : k) * a * b ^ 2 * c * d ^ 2 + (-1097 / 218240 : k) * a * b ^ 2 * f ^ 2
  + (-963 / 436480 : k) * a * b * d ^ 2 * f + (-3 / 2728 : k) * b ^ 2 * c * e ^ 2
  + (215 / 21824 : k) * b * c ^ 3 * f + (3 / 2728 : k) * b * c ^ 2 * d * e + (8 / 1705 : k) * b * e ^ 2 * f
  + (3 / 2728 : k) * c ^ 3 * d ^ 2 + (-893 / 54560 : k) * c ^ 2 * f ^ 2
  + (-3017 / 109120 : k) * c * d * e * f + (-3 / 682 : k) * d ^ 2 * e ^ 2

def quarticCostChamberBCDEFG9810_identityPartial1 (a b c d e f g : k) : k :=
  (-9 / 2728 : k) * a * b ^ 5 * e ^ 3 + (2889 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f
  + (-9 / 682 : k) * a * b ^ 4 * c * d * e ^ 2 + (-999 / 10912 : k) * a * b ^ 3 * c ^ 3 * d * f
  + (-153 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (-387 / 2728 : k) * a * b ^ 3 * c * e * f ^ 2
  + (6153 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 6820 : k) * a * b ^ 2 * c ^ 3 * d ^ 3
  + (5619 / 27280 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2
  + (29841 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2
  + (181 / 1364 : k) * a * b ^ 2 * e * f ^ 3 + (12153 / 54560 : k) * a * b * c ^ 2 * d ^ 3 * f
  + (63 / 1705 : k) * a * b * c * d ^ 4 * e + (174 / 1705 : k) * a * b * c * d * f ^ 3
  + (-6037 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2 + (36 / 1705 : k) * a * c ^ 2 * d ^ 5
  + (-2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2 + (-2889 / 13640 : k) * a * d ^ 4 * e * f
  + (-262 / 1705 : k) * a * d * f ^ 4 + (9 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3
  + (-3081 / 27280 : k) * b ^ 2 * c ^ 4 * e * f + (-9 / 341 : k) * b ^ 2 * c ^ 3 * d * e ^ 2
  + (-24 / 1705 : k) * b ^ 2 * c * e ^ 3 * f + (-36 / 341 : k) * b ^ 2 * d * e ^ 4
  + (681 / 3410 : k) * b * c ^ 5 * d * f + (81 / 3410 : k) * b * c ^ 4 * d ^ 2 * e
  + (355 / 682 : k) * b * c ^ 3 * e * f ^ 2 + (-4245 / 5456 : k) * b * c ^ 2 * d * e ^ 2 * f
  + (-432 / 1705 : k) * b * c * d ^ 2 * e ^ 3 + (-256 / 1705 : k) * b * e ^ 3 * f ^ 2
  + (36 / 1705 : k) * c ^ 5 * d ^ 3 + (-1143 / 6820 : k) * c ^ 4 * d * f ^ 2
  + (-7131 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (-54 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2
  + (-393 / 1705 : k) * c ^ 2 * e * f ^ 3 + (1143 / 1705 : k) * c * d * e ^ 2 * f ^ 2
  + (3369 / 3410 : k) * d ^ 2 * e ^ 3 * f

def quarticCostChamberBCDEFG9810_identityPartial2 (a b c d e f g : k) : k :=
  (-3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e
  + (9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2
  + (2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (9 / 2728 : k) * a * b ^ 5 * e ^ 3
  + (-2793 / 109120 : k) * a * b ^ 4 * c ^ 2 * e * f + (-9 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2
  + (6813 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f + (-207 / 13640 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e
  + (547 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2 + (-4809 / 109120 : k) * a * b ^ 3 * d * e ^ 2 * f
  + (-189 / 13640 : k) * a * b ^ 2 * c ^ 3 * d ^ 3 + (-1185 / 5456 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2
  + (-3081 / 13640 : k) * a * b ^ 2 * c * d ^ 2 * e * f + (48 / 1705 : k) * a * b ^ 2 * e * f ^ 3
  + (-5439 / 21824 : k) * a * b * c ^ 2 * d ^ 3 * f + (-63 / 1705 : k) * a * b * c * d ^ 4 * e
  + (1531 / 1705 : k) * a * b * c * d * f ^ 3 + (175 / 341 : k) * a * b * d ^ 2 * e * f ^ 2
  + (-36 / 1705 : k) * a * c ^ 2 * d ^ 5 + (2417 / 13640 : k) * a * c * d ^ 3 * f ^ 2
  + (2889 / 13640 : k) * a * d ^ 4 * e * f + (262 / 1705 : k) * a * d * f ^ 4
  + (-27 / 682 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (9531 / 27280 : k) * b ^ 2 * c ^ 4 * e * f
  + (27 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (276 / 1705 : k) * b ^ 2 * c * e ^ 3 * f
  + (36 / 341 : k) * b ^ 2 * d * e ^ 4 + (-2223 / 27280 : k) * b * c ^ 5 * d * f
  + (27 / 1705 : k) * b * c ^ 4 * d ^ 2 * e + (-8379 / 6820 : k) * b * c ^ 3 * e * f ^ 2
  + (3699 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * f + (252 / 1705 : k) * b * c * d ^ 2 * e ^ 3
  + (-27 / 3410 : k) * c ^ 5 * d ^ 3 + (-393 / 13640 : k) * c ^ 4 * d * f ^ 2
  + (-36 / 341 : k) * c ^ 3 * d ^ 2 * e * f + (-36 / 1705 : k) * c ^ 2 * d ^ 3 * e ^ 2
  + (1286 / 1705 : k) * c ^ 2 * e * f ^ 3 + (731 / 3410 : k) * c * d * e ^ 2 * f ^ 2
  + (-2889 / 3410 : k) * d ^ 2 * e ^ 3 * f

def quarticCostChamberBCDEFG9810_identityPartial3 (a b c d e f g : k) : k :=
  (3 / 27280 : k) * a ^ 2 * b ^ 5 * c * d * f + (-27 / 10912 : k) * a ^ 2 * b ^ 5 * d ^ 2 * e
  + (-9 / 5456 : k) * a ^ 2 * b ^ 4 * c * d ^ 3 + (-3291 / 218240 : k) * a ^ 2 * b ^ 4 * d * f ^ 2
  + (-2889 / 436480 : k) * a ^ 2 * b ^ 3 * d ^ 3 * f + (-3 / 3410 : k) * a * b ^ 4 * c ^ 2 * e * f
  + (45 / 2728 : k) * a * b ^ 4 * c * d * e ^ 2 + (3177 / 109120 : k) * a * b ^ 3 * c ^ 3 * d * f
  + (9 / 341 : k) * a * b ^ 3 * c ^ 2 * d ^ 2 * e + (3323 / 27280 : k) * a * b ^ 3 * c * e * f ^ 2
  + (-21 / 1705 : k) * a * b ^ 3 * d * e ^ 2 * f + (27 / 2728 : k) * a * b ^ 2 * c ^ 3 * d ^ 3
  + (153 / 13640 : k) * a * b ^ 2 * c ^ 2 * d * f ^ 2 + (-5193 / 109120 : k) * a * b ^ 2 * c * d ^ 2 * e * f
  + (-9 / 682 : k) * a * b ^ 2 * d ^ 3 * e ^ 2 + (-1097 / 6820 : k) * a * b ^ 2 * e * f ^ 3
  + (2889 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * f + (-963 / 13640 : k) * a * b * d ^ 2 * e * f ^ 2
  + (9 / 341 : k) * b ^ 3 * c ^ 2 * e ^ 3 + (-645 / 2728 : k) * b ^ 2 * c ^ 4 * e * f
  + (-9 / 682 : k) * b ^ 2 * c ^ 3 * d * e ^ 2 + (-252 / 1705 : k) * b ^ 2 * c * e ^ 3 * f
  + (-645 / 5456 : k) * b * c ^ 5 * d * f + (-27 / 682 : k) * b * c ^ 4 * d ^ 2 * e
  + (439 / 620 : k) * b * c ^ 3 * e * f ^ 2 + (8763 / 13640 : k) * b * c ^ 2 * d * e ^ 2 * f
  + (36 / 341 : k) * b * c * d ^ 2 * e ^ 3 + (256 / 1705 : k) * b * e ^ 3 * f ^ 2
  + (-9 / 682 : k) * c ^ 5 * d ^ 3 + (2679 / 13640 : k) * c ^ 4 * d * f ^ 2
  + (10011 / 27280 : k) * c ^ 3 * d ^ 2 * e * f + (18 / 341 : k) * c ^ 2 * d ^ 3 * e ^ 2
  + (-893 / 1705 : k) * c ^ 2 * e * f ^ 3 + (-3017 / 3410 : k) * c * d * e ^ 2 * f ^ 2
  + (-48 / 341 : k) * d ^ 2 * e ^ 3 * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #9: `BCDEFG` / `BF·CF·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*c*d*f^3`, 47 cofactor terms. -/
theorem quarticCostChamberBCDEFG9810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG9Face810 a b c d e f g + xiQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG9Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG9Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG9Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG9Face810 a b c d e f g)) =
      a * b * c * d * f ^ 3 := by
  have h1 : muQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG9Face810 a b c d e f g + xiQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG9Face810 a b c d e f g = quarticCostChamberBCDEFG9810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG9Cofactor810, muQuarticCostChamberBCDEFG9Face810, xiQuarticCostChamberBCDEFG9Cofactor810, xiQuarticCostChamberBCDEFG9Face810, quarticCostChamberBCDEFG9810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG9Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG9Face810 a b c d e f g = quarticCostChamberBCDEFG9810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG9Cofactor810, piQuarticCostChamberBCDEFG9Face810, kappaQuarticCostChamberBCDEFG9Cofactor810, kappaQuarticCostChamberBCDEFG9Face810, quarticCostChamberBCDEFG9810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG9Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG9Face810 a b c d e f g = quarticCostChamberBCDEFG9810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG9Cofactor810, n2QuarticCostChamberBCDEFG9Face810, quarticCostChamberBCDEFG9810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG9810_identityPartial1, quarticCostChamberBCDEFG9810_identityPartial2, quarticCostChamberBCDEFG9810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG9810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG9Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG9810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c * d * f ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact (hc hRll).elim
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

def muQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 436480 : k) * a * b * c * d ^ 3 + (-249 / 39680 : k) * b ^ 2 * c * e * g
  + (489 / 19840 : k) * b * c ^ 2 * d * g + (34299 / 872960 : k) * b * c * d * e ^ 2
  + (-223 / 2480 : k) * b * d * g ^ 2 + (-297 / 79360 : k) * c ^ 2 * d ^ 2 * e
  + (-15 / 248 : k) * d ^ 2 * e * g

def xiQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-12 : k) * c ^ 2 * e + 32 * e * g

def xiQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (1491 / 698368 : k) * a * b ^ 3 * d * e + (-1491 / 349184 : k) * a * b ^ 2 * c * d ^ 2
  + (-21 / 39680 : k) * b ^ 2 * c ^ 2 * g + (-9 / 31744 : k) * b ^ 2 * c * e ^ 2
  + (51 / 2480 : k) * b ^ 2 * g ^ 2 + (-1293 / 174592 : k) * b * c ^ 2 * d * e
  + (3491 / 109120 : k) * b * d * e * g + (9 / 31744 : k) * c ^ 3 * d ^ 2
  + (-209 / 19840 : k) * c * d ^ 2 * g

def piQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

def piQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 13967360 : k) * a * b * d ^ 3 + (51 / 79360 : k) * b ^ 2 * e * g + (3 / 3968 : k) * b * c * d * g
  + (4473 / 3491840 : k) * b * d * e ^ 2 + (-27 / 158720 : k) * c * d ^ 2 * e

def kappaQuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * d * e

def kappaQuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (-4473 / 1745920 : k) * a ^ 2 * b ^ 2 * d ^ 3 + (-153 / 79360 : k) * a * b ^ 3 * e * g
  + (193 / 158720 : k) * a * b ^ 2 * c * d * g + (-4473 / 436480 : k) * a * b ^ 2 * d * e ^ 2
  + (729 / 634880 : k) * a * b * c * d ^ 2 * e + (27 / 126976 : k) * a * c ^ 2 * d ^ 3
  + (-15 / 1984 : k) * a * d ^ 3 * g + (311 / 19840 : k) * b * c ^ 2 * e * g
  + (27 / 31744 : k) * b * c * e ^ 3 + (-51 / 1240 : k) * b * e * g ^ 2 + (1 / 19840 : k) * c ^ 3 * d * g
  + (-27 / 31744 : k) * c ^ 2 * d * e ^ 2 + (751 / 14880 : k) * c * d * g ^ 2
  + (15 / 496 : k) * d * e ^ 2 * g

def n2QuarticCostChamberBCDEFG10Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * d * g

def n2QuarticCostChamberBCDEFG10Cofactor810 (a b c d e f g : k) : k :=
  (1491 / 2793472 : k) * a ^ 2 * b ^ 3 * d ^ 2 + (-553 / 476160 : k) * a * b ^ 3 * c * g
  + (5667 / 1396736 : k) * a * b ^ 2 * c * d * e + (-3081 / 1396736 : k) * a * b * c ^ 2 * d ^ 2
  + (7561 / 436480 : k) * a * b * d ^ 2 * g + (-13 / 2480 : k) * b * c ^ 3 * g
  + (-9 / 31744 : k) * b * c ^ 2 * e ^ 2 + (227 / 14880 : k) * b * c * g ^ 2
  + (-17 / 992 : k) * b * e ^ 2 * g + (9 / 31744 : k) * c ^ 3 * d * e + (1547 / 59520 : k) * c * d * e * g

def quarticCostChamberBCDEFG10810_identityPartial1 (a b c d e f g : k) : k :=
  (4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (4473 / 872960 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (-4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5 + (-81 / 3968 : k) * a * b ^ 4 * c ^ 2 * e * g
  + (-27 / 31744 : k) * a * b ^ 4 * c * e ^ 3 + (153 / 2480 : k) * a * b ^ 4 * e * g ^ 2
  + (351 / 4960 : k) * a * b ^ 3 * c ^ 3 * d * g + (14913 / 218240 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2
  + (-363 / 2480 : k) * a * b ^ 3 * c * d * g ^ 2 + (2241 / 13640 : k) * a * b ^ 3 * d * e ^ 2 * g
  + (-567 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e
  + (-28947 / 218240 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (-34299 / 872960 : k) * a * b * c ^ 4 * d ^ 3
  + (18129 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * g + (27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2
  + (223 / 620 : k) * a * b * d ^ 3 * g ^ 2 + (297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e
  + (15 / 62 : k) * a * d ^ 4 * e * g + (39 / 1240 : k) * b ^ 2 * c ^ 4 * e * g
  + (27 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (-72 / 155 : k) * b ^ 2 * c ^ 2 * e * g ^ 2
  + (-543 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (102 / 155 : k) * b ^ 2 * e * g ^ 3
  + (-489 / 4960 : k) * b * c ^ 5 * d * g + (-1863 / 27280 : k) * b * c ^ 4 * d * e ^ 2
  + (178 / 155 : k) * b * c ^ 3 * d * g ^ 2 + (28119 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * g
  + (34299 / 54560 : k) * b * c * d * e ^ 4 + (-446 / 155 : k) * b * c * d * g ^ 3
  + (-283 / 682 : k) * b * d * e ^ 2 * g ^ 2 + (459 / 39680 : k) * c ^ 5 * d ^ 2 * e
  + (639 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (-297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3
  + (-1409 / 620 : k) * c * d ^ 2 * e * g ^ 2 + (-30 / 31 : k) * d ^ 2 * e ^ 3 * g

def quarticCostChamberBCDEFG10810_identityPartial2 (a b c d e f g : k) : k :=
  (-4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g
  + (-4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + (55161 / 6983680 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (-15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5
  + (-37 / 4960 : k) * a * b ^ 4 * c ^ 2 * e * g + (27 / 31744 : k) * a * b ^ 4 * c * e ^ 3
  + (-153 / 2480 : k) * a * b ^ 4 * e * g ^ 2 + (-2737 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g
  + (52191 / 1745920 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (205 / 1488 : k) * a * b ^ 3 * c * d * g ^ 2
  + (-6159 / 54560 : k) * a * b ^ 3 * d * e ^ 2 * g + (-243 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e
  + (6757 / 19840 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (22383 / 1745920 : k) * a * b * c ^ 4 * d ^ 3
  + (24513 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g + (-27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2
  + (1173 / 13640 : k) * a * b * d ^ 3 * g ^ 2 + (-297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e
  + (-15 / 62 : k) * a * d ^ 4 * e * g + (-39 / 248 : k) * b ^ 2 * c ^ 4 * e * g
  + (-81 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (103 / 124 : k) * b ^ 2 * c ^ 2 * e * g ^ 2
  + (-1497 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (-102 / 155 : k) * b ^ 2 * e * g ^ 3
  + (177 / 4960 : k) * b * c ^ 5 * d * g + (31293 / 436480 : k) * b * c ^ 4 * d * e ^ 2
  + (-989 / 1240 : k) * b * c ^ 3 * d * g ^ 2 + (-32929 / 54560 : k) * b * c ^ 2 * d * e ^ 2 * g
  + (-34299 / 54560 : k) * b * c * d * e ^ 4 + (1111 / 465 : k) * b * c * d * g ^ 3
  + (657 / 682 : k) * b * d * e ^ 2 * g ^ 2 + (-81 / 9920 : k) * c ^ 5 * d ^ 2 * e
  + (7 / 155 : k) * c ^ 3 * d ^ 2 * e * g + (297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3
  + (134 / 93 : k) * c * d ^ 2 * e * g ^ 2 + (30 / 31 : k) * d ^ 2 * e ^ 3 * g

def quarticCostChamberBCDEFG10810_identityPartial3 (a b c d e f g : k) : k :=
  (4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (-553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g
  + (-81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + (-18189 / 1396736 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (553 / 19840 : k) * a * b ^ 4 * c ^ 2 * e * g
  + (-71 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g + (-34299 / 349184 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2
  + (4 / 465 : k) * a * b ^ 3 * c * d * g ^ 2 + (-51 / 992 : k) * a * b ^ 3 * d * e ^ 2 * g
  + (81 / 15872 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-2269 / 10912 : k) * a * b ^ 2 * c * d ^ 2 * e * g
  + (9243 / 349184 : k) * a * b * c ^ 4 * d ^ 3 + (-60771 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g
  + (7561 / 13640 : k) * a * b * d ^ 3 * g ^ 2 + (39 / 310 : k) * b ^ 2 * c ^ 4 * e * g
  + (27 / 3968 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (-227 / 620 : k) * b ^ 2 * c ^ 2 * e * g ^ 2
  + (51 / 124 : k) * b ^ 2 * c * e ^ 3 * g + (39 / 620 : k) * b * c ^ 5 * d * g
  + (-27 / 7936 : k) * b * c ^ 4 * d * e ^ 2 + (-87 / 248 : k) * b * c ^ 3 * d * g ^ 2
  + (-2119 / 4960 : k) * b * c ^ 2 * d * e ^ 2 * g + (227 / 465 : k) * b * c * d * g ^ 3
  + (-17 / 31 : k) * b * d * e ^ 2 * g ^ 2 + (-27 / 7936 : k) * c ^ 5 * d ^ 2 * e
  + (-751 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (1547 / 1860 : k) * c * d ^ 2 * e * g ^ 2

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #10: `BCDEFG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*d^3*g^2`, 46 cofactor terms. -/
theorem quarticCostChamberBCDEFG10810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG10Face810 a b c d e f g + xiQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG10Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG10Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG10Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG10Face810 a b c d e f g)) =
      a * b * d ^ 3 * g ^ 2 := by
  have h1 : muQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG10Face810 a b c d e f g + xiQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG10Face810 a b c d e f g = quarticCostChamberBCDEFG10810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEFG10Cofactor810, muQuarticCostChamberBCDEFG10Face810, xiQuarticCostChamberBCDEFG10Cofactor810, xiQuarticCostChamberBCDEFG10Face810, quarticCostChamberBCDEFG10810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG10Face810 a b c d e f g + kappaQuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG10Face810 a b c d e f g = quarticCostChamberBCDEFG10810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEFG10Cofactor810, piQuarticCostChamberBCDEFG10Face810, kappaQuarticCostChamberBCDEFG10Cofactor810, kappaQuarticCostChamberBCDEFG10Face810, quarticCostChamberBCDEFG10810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEFG10Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG10Face810 a b c d e f g = quarticCostChamberBCDEFG10810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEFG10Cofactor810, n2QuarticCostChamberBCDEFG10Face810, quarticCostChamberBCDEFG10810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEFG10810_identityPartial1, quarticCostChamberBCDEFG10810_identityPartial2, quarticCostChamberBCDEFG10810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG10810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG10Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG10810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * d ^ 3 * g ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact (ha hLll).elim
      ·
        exact (hb hRll).elim
    ·
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hRl)
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  -a * d ^ 2 - c ^ 3 + 8 * c * g + 4 * e ^ 2

def muQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (1 / 3 : k) * f * g

def xiQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * d * f + (-3 : k) * c ^ 2 * e + 8 * e * g

def xiQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (1 / 48 : k) * c ^ 2 * d + (2 / 3 : k) * d * g + (1 / 2 : k) * e * f

def piQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  8 * a * c * d ^ 2 + (-16 : k) * a * f ^ 2 + 3 * c ^ 4 + (-16 : k) * c ^ 2 * g + (-32 : k) * c * e ^ 2
  + 64 * g ^ 2

def piQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 24 : k) * c * f

def kappaQuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  c * f + d * e

def kappaQuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  a * c * d ^ 2 + (-2 / 3 : k) * a * f ^ 2 + (1 / 8 : k) * c ^ 4 + (-1 / 3 : k) * c ^ 2 * g

def n2QuarticCostChamberBCDEFG11Face810 (a b c d e f g : k) : k :=
  (-3 : k) * c ^ 2 * d + 8 * d * g + 8 * e * f

def n2QuarticCostChamberBCDEFG11Cofactor810 (a b c d e f g : k) : k :=
  (5 / 24 : k) * a * d * f + (1 / 48 : k) * c ^ 2 * e + (-2 / 3 : k) * e * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #11: `BCDEFG` / `CF·CG·DD·DE·EE·CCC`, target `a*c*d^3*e`, 12 cofactor terms. -/
theorem quarticCostChamberBCDEFG11810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      xiQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      kappaQuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEFG11Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG11Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG11Face810 a b c d e f g =
      a * c * d ^ 3 * e := by
  simp only [muQuarticCostChamberBCDEFG11Face810, xiQuarticCostChamberBCDEFG11Face810, piQuarticCostChamberBCDEFG11Face810, kappaQuarticCostChamberBCDEFG11Face810, n2QuarticCostChamberBCDEFG11Face810, muQuarticCostChamberBCDEFG11Cofactor810, xiQuarticCostChamberBCDEFG11Cofactor810, piQuarticCostChamberBCDEFG11Cofactor810, kappaQuarticCostChamberBCDEFG11Cofactor810, n2QuarticCostChamberBCDEFG11Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG11810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG11Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG11810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * c * d ^ 3 * e = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact (ha hLll).elim
      ·
        exact (hc hRll).elim
    ·
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hRl)
  ·
    exact (he hR).elim

def muQuarticCostChamberBCDEFG12Face810 (a b c d e f g : k) : k :=
  -a * d ^ 2 - c ^ 3 + 8 * c * g

def muQuarticCostChamberBCDEFG12Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 11 : k) * c * d

def piQuarticCostChamberBCDEFG12Face810 (a b c d e f g : k) : k :=
  8 * a * c * d ^ 2 + 3 * c ^ 4 + (-16 : k) * c ^ 2 * g + 64 * g ^ 2

def piQuarticCostChamberBCDEFG12Cofactor810 (a b c d e f g : k) : k :=
  (1 / 11 : k) * d

def n2QuarticCostChamberBCDEFG12Face810 (a b c d e f g : k) : k :=
  (-3 : k) * c ^ 2 * d + 8 * d * g

def n2QuarticCostChamberBCDEFG12Cofactor810 (a b c d e f g : k) : k :=
  (2 / 11 : k) * c ^ 2 + (-8 / 11 : k) * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #12: `BCDEFG` / `CG·DD·CCC`, target `a*c*d^3`, 4 cofactor terms. -/
theorem quarticCostChamberBCDEFG12810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDEFG12Cofactor810 a b c d e f g * muQuarticCostChamberBCDEFG12Face810 a b c d e f g +
      piQuarticCostChamberBCDEFG12Cofactor810 a b c d e f g * piQuarticCostChamberBCDEFG12Face810 a b c d e f g +
      n2QuarticCostChamberBCDEFG12Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEFG12Face810 a b c d e f g =
      a * c * d ^ 3 := by
  simp only [muQuarticCostChamberBCDEFG12Face810, piQuarticCostChamberBCDEFG12Face810, n2QuarticCostChamberBCDEFG12Face810, muQuarticCostChamberBCDEFG12Cofactor810, piQuarticCostChamberBCDEFG12Cofactor810, n2QuarticCostChamberBCDEFG12Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEFG12810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEFG12Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEFG12Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEFG12Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEFG12810_identity a b c d e f g
  rw [hmu, hpi, hn2] at hid
  have hz : a * c * d ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hc hRl).elim
  ·
    exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

def muQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 436480 : k) * a * b * c * d ^ 3 + (-249 / 39680 : k) * b ^ 2 * c * e * g
  + (489 / 19840 : k) * b * c ^ 2 * d * g + (34299 / 872960 : k) * b * c * d * e ^ 2
  + (-223 / 2480 : k) * b * d * g ^ 2 + (-297 / 79360 : k) * c ^ 2 * d ^ 2 * e
  + (-15 / 248 : k) * d ^ 2 * e * g

def xiQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-12 : k) * c ^ 2 * e + 32 * e * g

def xiQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (1491 / 698368 : k) * a * b ^ 3 * d * e + (-1491 / 349184 : k) * a * b ^ 2 * c * d ^ 2
  + (-21 / 39680 : k) * b ^ 2 * c ^ 2 * g + (-9 / 31744 : k) * b ^ 2 * c * e ^ 2
  + (51 / 2480 : k) * b ^ 2 * g ^ 2 + (-1293 / 174592 : k) * b * c ^ 2 * d * e
  + (3491 / 109120 : k) * b * d * e * g + (9 / 31744 : k) * c ^ 3 * d ^ 2
  + (-209 / 19840 : k) * c * d ^ 2 * g

def piQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 256 * a * b * d * e
  + 128 * a * c * d ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

def piQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (4473 / 13967360 : k) * a * b * d ^ 3 + (51 / 79360 : k) * b ^ 2 * e * g + (3 / 3968 : k) * b * c * d * g
  + (4473 / 3491840 : k) * b * d * e ^ 2 + (-27 / 158720 : k) * c * d ^ 2 * e

def kappaQuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * d * e

def kappaQuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (-4473 / 1745920 : k) * a ^ 2 * b ^ 2 * d ^ 3 + (-153 / 79360 : k) * a * b ^ 3 * e * g
  + (193 / 158720 : k) * a * b ^ 2 * c * d * g + (-4473 / 436480 : k) * a * b ^ 2 * d * e ^ 2
  + (729 / 634880 : k) * a * b * c * d ^ 2 * e + (27 / 126976 : k) * a * c ^ 2 * d ^ 3
  + (-15 / 1984 : k) * a * d ^ 3 * g + (311 / 19840 : k) * b * c ^ 2 * e * g
  + (27 / 31744 : k) * b * c * e ^ 3 + (-51 / 1240 : k) * b * e * g ^ 2 + (1 / 19840 : k) * c ^ 3 * d * g
  + (-27 / 31744 : k) * c ^ 2 * d * e ^ 2 + (751 / 14880 : k) * c * d * g ^ 2
  + (15 / 496 : k) * d * e ^ 2 * g

def n2QuarticCostChamberBCDEG13Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * d * g

def n2QuarticCostChamberBCDEG13Cofactor810 (a b c d e f g : k) : k :=
  (1491 / 2793472 : k) * a ^ 2 * b ^ 3 * d ^ 2 + (-553 / 476160 : k) * a * b ^ 3 * c * g
  + (5667 / 1396736 : k) * a * b ^ 2 * c * d * e + (-3081 / 1396736 : k) * a * b * c ^ 2 * d ^ 2
  + (7561 / 436480 : k) * a * b * d ^ 2 * g + (-13 / 2480 : k) * b * c ^ 3 * g
  + (-9 / 31744 : k) * b * c ^ 2 * e ^ 2 + (227 / 14880 : k) * b * c * g ^ 2
  + (-17 / 992 : k) * b * e ^ 2 * g + (9 / 31744 : k) * c ^ 3 * d * e + (1547 / 59520 : k) * c * d * e * g

def quarticCostChamberBCDEG13810_identityPartial1 (a b c d e f g : k) : k :=
  (4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (4473 / 872960 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (-4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5 + (-81 / 3968 : k) * a * b ^ 4 * c ^ 2 * e * g
  + (-27 / 31744 : k) * a * b ^ 4 * c * e ^ 3 + (153 / 2480 : k) * a * b ^ 4 * e * g ^ 2
  + (351 / 4960 : k) * a * b ^ 3 * c ^ 3 * d * g + (14913 / 218240 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2
  + (-363 / 2480 : k) * a * b ^ 3 * c * d * g ^ 2 + (2241 / 13640 : k) * a * b ^ 3 * d * e ^ 2 * g
  + (-567 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e
  + (-28947 / 218240 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (-34299 / 872960 : k) * a * b * c ^ 4 * d ^ 3
  + (18129 / 109120 : k) * a * b * c ^ 2 * d ^ 3 * g + (27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2
  + (223 / 620 : k) * a * b * d ^ 3 * g ^ 2 + (297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e
  + (15 / 62 : k) * a * d ^ 4 * e * g + (39 / 1240 : k) * b ^ 2 * c ^ 4 * e * g
  + (27 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (-72 / 155 : k) * b ^ 2 * c ^ 2 * e * g ^ 2
  + (-543 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (102 / 155 : k) * b ^ 2 * e * g ^ 3
  + (-489 / 4960 : k) * b * c ^ 5 * d * g + (-1863 / 27280 : k) * b * c ^ 4 * d * e ^ 2
  + (178 / 155 : k) * b * c ^ 3 * d * g ^ 2 + (28119 / 27280 : k) * b * c ^ 2 * d * e ^ 2 * g
  + (34299 / 54560 : k) * b * c * d * e ^ 4 + (-446 / 155 : k) * b * c * d * g ^ 3
  + (-283 / 682 : k) * b * d * e ^ 2 * g ^ 2 + (459 / 39680 : k) * c ^ 5 * d ^ 2 * e
  + (639 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (-297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3
  + (-1409 / 620 : k) * c * d ^ 2 * e * g ^ 2 + (-30 / 31 : k) * d ^ 2 * e ^ 3 * g

def quarticCostChamberBCDEG13810_identityPartial2 (a b c d e f g : k) : k :=
  (-4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g
  + (-4473 / 698368 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + (55161 / 6983680 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (-15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (4473 / 109120 : k) * a ^ 2 * b * c * d ^ 5
  + (-37 / 4960 : k) * a * b ^ 4 * c ^ 2 * e * g + (27 / 31744 : k) * a * b ^ 4 * c * e ^ 3
  + (-153 / 2480 : k) * a * b ^ 4 * e * g ^ 2 + (-2737 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g
  + (52191 / 1745920 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (205 / 1488 : k) * a * b ^ 3 * c * d * g ^ 2
  + (-6159 / 54560 : k) * a * b ^ 3 * d * e ^ 2 * g + (-243 / 158720 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e
  + (6757 / 19840 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (22383 / 1745920 : k) * a * b * c ^ 4 * d ^ 3
  + (24513 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g + (-27 / 3968 : k) * a * b * c * d ^ 3 * e ^ 2
  + (1173 / 13640 : k) * a * b * d ^ 3 * g ^ 2 + (-297 / 19840 : k) * a * c ^ 2 * d ^ 4 * e
  + (-15 / 62 : k) * a * d ^ 4 * e * g + (-39 / 248 : k) * b ^ 2 * c ^ 4 * e * g
  + (-81 / 7936 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (103 / 124 : k) * b ^ 2 * c ^ 2 * e * g ^ 2
  + (-1497 / 4960 : k) * b ^ 2 * c * e ^ 3 * g + (-102 / 155 : k) * b ^ 2 * e * g ^ 3
  + (177 / 4960 : k) * b * c ^ 5 * d * g + (31293 / 436480 : k) * b * c ^ 4 * d * e ^ 2
  + (-989 / 1240 : k) * b * c ^ 3 * d * g ^ 2 + (-32929 / 54560 : k) * b * c ^ 2 * d * e ^ 2 * g
  + (-34299 / 54560 : k) * b * c * d * e ^ 4 + (1111 / 465 : k) * b * c * d * g ^ 3
  + (657 / 682 : k) * b * d * e ^ 2 * g ^ 2 + (-81 / 9920 : k) * c ^ 5 * d ^ 2 * e
  + (7 / 155 : k) * c ^ 3 * d ^ 2 * e * g + (297 / 4960 : k) * c ^ 2 * d ^ 2 * e ^ 3
  + (134 / 93 : k) * c * d ^ 2 * e * g ^ 2 + (30 / 31 : k) * d ^ 2 * e ^ 3 * g

def quarticCostChamberBCDEG13810_identityPartial3 (a b c d e f g : k) : k :=
  (4473 / 2793472 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (-553 / 158720 : k) * a ^ 2 * b ^ 5 * c * d * g
  + (-81 / 126976 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e
  + (-18189 / 1396736 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3
  + (15069 / 218240 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (553 / 19840 : k) * a * b ^ 4 * c ^ 2 * e * g
  + (-71 / 39680 : k) * a * b ^ 3 * c ^ 3 * d * g + (-34299 / 349184 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2
  + (4 / 465 : k) * a * b ^ 3 * c * d * g ^ 2 + (-51 / 992 : k) * a * b ^ 3 * d * e ^ 2 * g
  + (81 / 15872 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-2269 / 10912 : k) * a * b ^ 2 * c * d ^ 2 * e * g
  + (9243 / 349184 : k) * a * b * c ^ 4 * d ^ 3 + (-60771 / 218240 : k) * a * b * c ^ 2 * d ^ 3 * g
  + (7561 / 13640 : k) * a * b * d ^ 3 * g ^ 2 + (39 / 310 : k) * b ^ 2 * c ^ 4 * e * g
  + (27 / 3968 : k) * b ^ 2 * c ^ 3 * e ^ 3 + (-227 / 620 : k) * b ^ 2 * c ^ 2 * e * g ^ 2
  + (51 / 124 : k) * b ^ 2 * c * e ^ 3 * g + (39 / 620 : k) * b * c ^ 5 * d * g
  + (-27 / 7936 : k) * b * c ^ 4 * d * e ^ 2 + (-87 / 248 : k) * b * c ^ 3 * d * g ^ 2
  + (-2119 / 4960 : k) * b * c ^ 2 * d * e ^ 2 * g + (227 / 465 : k) * b * c * d * g ^ 3
  + (-17 / 31 : k) * b * d * e ^ 2 * g ^ 2 + (-27 / 7936 : k) * c ^ 5 * d ^ 2 * e
  + (-751 / 2480 : k) * c ^ 3 * d ^ 2 * e * g + (1547 / 1860 : k) * c * d ^ 2 * e * g ^ 2

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #13: `BCDEG` / `BG·CG·DD·DE·EE·BBB·BBC·BCC·CCC`, target `a*b*d^3*g^2`, 46 cofactor terms. -/
theorem quarticCostChamberBCDEG13810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * muQuarticCostChamberBCDEG13Face810 a b c d e f g + xiQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEG13Face810 a b c d e f g) +
      (piQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * piQuarticCostChamberBCDEG13Face810 a b c d e f g + kappaQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEG13Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDEG13Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEG13Face810 a b c d e f g)) =
      a * b * d ^ 3 * g ^ 2 := by
  have h1 : muQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * muQuarticCostChamberBCDEG13Face810 a b c d e f g + xiQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * xiQuarticCostChamberBCDEG13Face810 a b c d e f g = quarticCostChamberBCDEG13810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDEG13Cofactor810, muQuarticCostChamberBCDEG13Face810, xiQuarticCostChamberBCDEG13Cofactor810, xiQuarticCostChamberBCDEG13Face810, quarticCostChamberBCDEG13810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * piQuarticCostChamberBCDEG13Face810 a b c d e f g + kappaQuarticCostChamberBCDEG13Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDEG13Face810 a b c d e f g = quarticCostChamberBCDEG13810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDEG13Cofactor810, piQuarticCostChamberBCDEG13Face810, kappaQuarticCostChamberBCDEG13Cofactor810, kappaQuarticCostChamberBCDEG13Face810, quarticCostChamberBCDEG13810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDEG13Cofactor810 a b c d e f g * n2QuarticCostChamberBCDEG13Face810 a b c d e f g = quarticCostChamberBCDEG13810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDEG13Cofactor810, n2QuarticCostChamberBCDEG13Face810, quarticCostChamberBCDEG13810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDEG13810_identityPartial1, quarticCostChamberBCDEG13810_identityPartial2, quarticCostChamberBCDEG13810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDEG13810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDEG13Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDEG13810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * d ^ 3 * g ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact (ha hLll).elim
      ·
        exact (hb hRll).elim
    ·
      exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hRl)
  ·
    exact hg ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (306375 / 10621952 : k) * a ^ 2 * b ^ 2 * d ^ 2 + (-8489786204025 / 236733513191538688 : k) * a * b ^ 6
  + (24203652502940644395439437237 / 86501963629035729667428343808 : k) * a * b ^ 3 * c * d
  + (-86627058343584314136045208013 / 86501963629035729667428343808 : k) * a * b ^ 2 * d * f
  + (-41925 / 2655488 : k) * a * c ^ 2 * d ^ 2 + (102125 / 331936 : k) * a * d ^ 2 * g
  + (1818424565942034485326844391 / 1704472189734694180638982144 : k) * b ^ 4 * c ^ 2
  + (-57356709145669456587333265 / 168949147712960409506695984 : k) * b ^ 4 * g
  + (-104626839732757891739784367 / 24135592530422915643813712 : k) * b ^ 3 * c * f
  + (83918472870072414063667556095 / 21625490907258932416857085952 : k) * b ^ 2 * f ^ 2
  + (-6517147829218703765241 / 12672278815014380097536 : k) * b * c ^ 3 * d
  + (60104648120576522411393 / 36432801593166342780416 : k) * b * c * d * g
  + (1509161155411064241 / 1613482895744591872 : k) * c ^ 2 * d * f
  + (-3535662523195187727 / 311695559405205248 : k) * d * f * g

def xiQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 24 * a * b * c * d + (-32 : k) * a * d * f + 36 * b ^ 2 * c ^ 2
  + (-32 : k) * b ^ 2 * g + (-80 : k) * b * c * f + 64 * f ^ 2

def xiQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (71741522324055 / 236733513191538688 : k) * a * b ^ 4 * c
  + (-7304570789997530201916654721 / 216254909072589324168570859520 : k) * a * b ^ 3 * f
  + (-1075 / 230912 : k) * a * b * c ^ 2 * d + (-50525 / 663872 : k) * a * b * d * g
  + (-63425 / 1327744 : k) * a * c * d * f
  + (10161435150145635422189704895 / 43250981814517864833714171904 : k) * b ^ 2 * c ^ 3
  + (-5756361821531483068344382367 / 10812745453629466208428542976 : k) * b ^ 2 * c * g
  + (-85363223735078739635607699 / 93535860325514413567720960 : k) * b * c ^ 2 * f
  + (12662968548288402181 / 17143255767286288640 : k) * b * f * g
  + (12662968548288402181 / 17143255767286288640 : k) * c * f ^ 2

def piQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (-134758511175 / 13925500775972864 : k) * a * b ^ 3 * d + (-1075 / 129536 : k) * a * c * d ^ 2
  + (6827421669225 / 55702003103891456 : k) * b ^ 4 * c
  + (-95296593996145079 / 24662061874247942144 : k) * b ^ 3 * f
  + (-776567937635417 / 536131779874955264 : k) * b * c ^ 2 * d
  + (-29795570675430877 / 1541378867140496384 : k) * b * d * g
  + (-2058412336941 / 130741665646592 : k) * c * d * f

def kappaQuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (-404275533525 / 13925500775972864 : k) * a ^ 2 * b ^ 4 * d
  + (80625 / 1327744 : k) * a ^ 2 * b * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 2 * d ^ 2 * f
  + (37406699582145 / 72841080982011904 : k) * a * b ^ 5 * c
  + (-77674561570759903607185217187 / 865019636290357296674283438080 : k) * a * b ^ 4 * f
  + (119961310791003313144938941 / 172486467854507935528271872 : k) * a * b ^ 2 * c ^ 2 * d
  + (709924630645330306640845 / 1369595275155422342995968 : k) * a * b ^ 2 * d * g
  + (-338277241374667905607843859 / 165206194860648834353377280 : k) * a * b * c * d * f
  + (3035389292883998949 / 4285813941821572160 : k) * a * d * f ^ 2
  + (2202913219370688464780866053 / 4739833623508807105064566784 : k) * b ^ 3 * c ^ 3
  + (10104958976132890659839897 / 9978479861846648498970624 : k) * b ^ 3 * c * g
  + (-1303312252875391504269272559 / 620530585574144402205368320 : k) * b ^ 2 * c ^ 2 * f
  + (-1494851127721140434183 / 1234314415244612782080 : k) * b ^ 2 * f * g
  + (152547741673630055616892297 / 48926450016422924020038656 : k) * b * c * f ^ 2
  + (-22575 / 713728 : k) * c ^ 4 * d + (28936180369735246397 / 246862883048922556416 : k) * c ^ 2 * d * g
  + (33476795979037137983 / 5445504773137997568 : k) * d * g ^ 2
  + (-12662968548288402181 / 8571627883643144320 : k) * f ^ 3

def n2QuarticCostChamberBCDFG14Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 7 * b ^ 3 * c + (-12 : k) * b ^ 2 * f + (-12 : k) * c ^ 2 * d + 32 * d * g

def n2QuarticCostChamberBCDFG14Cofactor810 (a b c d e f g : k) : k :=
  (134758511175 / 6962750387986432 : k) * a ^ 2 * b ^ 5 + (-433225 / 10621952 : k) * a ^ 2 * b ^ 2 * c * d
  + (76325 / 663872 : k) * a ^ 2 * b * d * f
  + (-148217539479813251853480729 / 350920744945378213660966912 : k) * a * b ^ 3 * c ^ 2
  + (-15964966090082343775487 / 69640437719767237779456 : k) * a * b ^ 3 * g
  + (393184403423561718068756079 / 175460372472689106830483456 : k) * a * b ^ 2 * c * f
  + (-53411281163041567780899 / 19022156599380865874944 : k) * a * b * f ^ 2
  + (-3225 / 115456 : k) * a * c ^ 3 * d + (-13975 / 331936 : k) * a * c * d * g
  + (357111649996001035995 / 1810325545002054299648 : k) * b * c ^ 4
  + (-648744782492956030092913907 / 394785838063550490368587776 : k) * b * c ^ 2 * g
  + (-709924630645330306640845 / 128399557045820844655872 : k) * b * g ^ 2
  + (-12592848312077406207 / 27429209227658061824 : k) * c ^ 3 * f
  + (131906475228771548681 / 23143395285836489664 : k) * c * f * g

def quarticCostChamberBCDFG14810_identityPartial1 (a b c d e f g : k) : k :=
  (919125 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-306375 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f
  + (-15043370349015 / 14795844574471168 : k) * a ^ 2 * b ^ 8 * c
  + (21975755396139435971852270913 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f
  + (398118802790466194565788913 / 462577345609816736189456384 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d
  + (151575 / 663872 : k) * a ^ 2 * b ^ 5 * d * g
  + (-20273364047907900355616031 / 3424653924961626126049280 : k) * a ^ 2 * b ^ 4 * c * d * f
  + (15207242368958553231 / 1672512757784028160 : k) * a ^ 2 * b ^ 3 * d * f ^ 2
  + (-364425 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2
  + (3225 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g
  + (-289175 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (-1075 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g
  + (63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2
  + (45651084107159531250336307461 / 18210939711375943087879651328 : k) * a * b ^ 6 * c ^ 3
  + (87142350193274227539 / 153477295770989425664 : k) * a * b ^ 6 * c * g
  + (-105712157500132227807472458537 / 5274509977380227418745630720 : k) * a * b ^ 5 * c ^ 2 * f
  + (21366563471104860432053675553 / 13515931817036832760535678720 : k) * a * b ^ 5 * f * g
  + (389482770919523749602714308541 / 8317496502791897083406571520 : k) * a * b ^ 4 * c * f ^ 2
  + (7146387902934472338125782377 / 2544175400853992049042010112 : k) * a * b ^ 3 * c ^ 4 * d
  + (-66545120632391553582681257 / 45431703586678429447178752 : k) * a * b ^ 3 * c ^ 2 * d * g
  + (50525 / 20746 : k) * a * b ^ 3 * d * g ^ 2
  + (-81322818830239985319 / 2449036538183755520 : k) * a * b ^ 3 * f ^ 3
  + (-5736622049976496092151038979 / 289110841006135460118410240 : k) * a * b ^ 2 * c ^ 3 * d * f
  + (-9480398995258144761969591 / 256966649245918718592640 : k) * a * b ^ 2 * c * d * f * g
  + (34165560315753049348025344349 / 795054812766872515325628160 : k) * a * b * c ^ 2 * d * f ^ 2
  + (133371853726969312261 / 2142906970910786080 : k) * a * b * d * f ^ 2 * g
  + (41925 / 663872 : k) * a * c ^ 5 * d ^ 2 + (-72025 / 41492 : k) * a * c ^ 3 * d ^ 2 * g
  + (102125 / 10373 : k) * a * c * d ^ 2 * g ^ 2
  + (-1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3
  + (362483143924252749876309341067 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5
  + (95302997651225907569791322841 / 10812745453629466208428542976 : k) * b ^ 4 * c ^ 3 * g
  + (29602276306665925073 / 4796165492843419552 : k) * b ^ 4 * c * g ^ 2
  + (-66247321088877544520293841499 / 1930847402433833251505096960 : k) * b ^ 3 * c ^ 4 * f
  + (-4466366059525506282488141 / 110735496960713383697120 : k) * b ^ 3 * c ^ 2 * f * g
  + (-12662968548288402181 / 535726742727696520 : k) * b ^ 3 * f * g ^ 2
  + (22514989088246482852509668739 / 227158517933392147235893760 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (34095289019550827906752641 / 4622411702132979740265280 : k) * b ^ 2 * c * f ^ 2 * g
  + (6517147829218703765241 / 3168069703753595024384 : k) * b * c ^ 6 * d
  + (-6562470256018959656623 / 284631262446612052972 : k) * b * c ^ 4 * d * g
  + (60104648120576522411393 / 1138525049786448211888 : k) * b * c ^ 2 * d * g ^ 2
  + (-5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3
  + (12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g
  + (-1509161155411064241 / 403370723936147968 : k) * c ^ 5 * d * f
  + (32274013698567578547 / 428581394182157216 : k) * c ^ 3 * d * f * g
  + (-3535662523195187727 / 9740486231412664 : k) * c * d * f * g ^ 2
  + (12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

def quarticCostChamberBCDFG14810_identityPartial2 (a b c d e f g : k) : k :=
  (-404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d
  + (190275 / 5310976 : k) * a ^ 3 * b ^ 4 * c * d ^ 2 + (-151575 / 1327744 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f
  + (104310699962295 / 118366756595769344 : k) * a ^ 2 * b ^ 8 * c
  + (-21925530089258656389769451163 / 216254909072589324168570859520 : k) * a ^ 2 * b ^ 7 * f
  + (7044131506046122708369531537 / 10176701603415968196168040448 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d
  + (628379294481695956874533 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g
  + (-3810822752374450789365119719 / 1817268143467137177887150080 : k) * a ^ 2 * b ^ 4 * c * d * f
  + (1056202824840943267347 / 1486105984326630146480 : k) * a ^ 2 * b ^ 3 * d * f ^ 2
  + (-87075 / 663872 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2
  + (117175 / 82984 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g
  + (747125 / 331936 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f
  + (-151575 / 41492 : k) * a ^ 2 * b * d ^ 2 * f * g + (-63425 / 41492 : k) * a ^ 2 * c * d ^ 2 * f ^ 2
  + (155626859453639970536334149799 / 346007854516142918669713375232 : k) * a * b ^ 6 * c ^ 3
  + (10347213948186673629137837 / 9978479861846648498970624 : k) * a * b ^ 6 * c * g
  + (-44019624995593251425232075003 / 61787116877882664048163102720 : k) * a * b ^ 5 * c ^ 2 * f
  + (-4215502734257277845144973117101 / 973147090826651958758568867840 : k) * a * b ^ 5 * f * g
  + (-661758235232847097126742823 / 2350596837745536132267074560 : k) * a * b ^ 4 * c * f ^ 2
  + (-513401819752361576574050265 / 62053058557414440220536832 : k) * a * b ^ 3 * c ^ 4 * d
  + (49956985392305014269906269557 / 2862197325960741055172261376 : k) * a * b ^ 3 * c ^ 2 * d * g
  + (689750356046346517189867 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2
  + (-5802984711411749625657 / 11888847874613041171840 : k) * a * b ^ 3 * f ^ 3
  + (151934614432978587766505530199 / 3180219251067490061302512640 : k) * a * b ^ 2 * c ^ 3 * d * f
  + (-5138060070301936480675711793 / 98020456368518529286721280 : k) * a * b ^ 2 * c * d * f * g
  + (-30079600313357745180524257067 / 397527406383436257662814080 : k) * a * b * c ^ 2 * d * f ^ 2
  + (446030677695116319557 / 16153325916593805940 : k) * a * b * d * f ^ 2 * g
  + (-3225 / 8096 : k) * a * c ^ 5 * d ^ 2 + (1075 / 506 : k) * a * c ^ 3 * d ^ 2 * g
  + (-2150 / 253 : k) * a * c * d ^ 2 * g ^ 2
  + (1300072803345640971 / 48702431157063320 : k) * a * c * d * f ^ 3
  + (-481929070825741485105660543957 / 86501963629035729667428343808 : k) * b ^ 4 * c ^ 5
  + (47578571514647720326763825629 / 17693583469575490159246706688 : k) * b ^ 4 * c ^ 3 * g
  + (10144097124616423428348197 / 311827495682707765592832 : k) * b ^ 4 * c * g ^ 2
  + (616185350475785252973327994947 / 15446779219470666012040775680 : k) * b ^ 3 * c ^ 4 * f
  + (-14073502449611371011668000966051 / 729860318119988969068926650880 : k) * b ^ 3 * c ^ 2 * f * g
  + (-175772958624644502907757 / 4115370418135283482560 : k) * b ^ 3 * f * g ^ 2
  + (-1808317652048889402615960279 / 17283800277540706854904960 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (109153969120539636339947328713 / 1788873328725463159482663360 : k) * b ^ 2 * c * f ^ 2 * g
  + (425930971681404159 / 1373837685929572864 : k) * b * c ^ 6 * d
  + (-4994646827546302311415 / 1678425582298311694848 : k) * b * c ^ 4 * d * g
  + (-356067772626052476285271 / 5349981543575868527328 : k) * b * c ^ 2 * d * g ^ 2
  + (5838709603278819518951144461 / 49690925797929532207851760 : k) * b * c ^ 2 * f ^ 3
  + (709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3
  + (-12662968548288402181 / 267863371363848260 : k) * b * f ^ 3 * g
  + (-10068775161332331 / 5695433809729664 : k) * c ^ 5 * d * f
  + (60029289149566436741 / 7714465095278829888 : k) * c ^ 3 * d * f * g
  + (30733286380816738835 / 170172024160562424 : k) * c * d * f * g ^ 2
  + (-12662968548288402181 / 267863371363848260 : k) * c * f ^ 4

def quarticCostChamberBCDFG14810_identityPartial3 (a b c d e f g : k) : k :=
  (404275533525 / 6962750387986432 : k) * a ^ 3 * b ^ 7 * d
  + (-1299675 / 10621952 : k) * a ^ 3 * b ^ 4 * c * d ^ 2
  + (228975 / 663872 : k) * a ^ 3 * b ^ 3 * d ^ 2 * f
  + (943309578225 / 6962750387986432 : k) * a ^ 2 * b ^ 8 * c
  + (-404275533525 / 1740687596996608 : k) * a ^ 2 * b ^ 7 * f
  + (-544922247152978585821271987 / 350920744945378213660966912 : k) * a ^ 2 * b ^ 5 * c ^ 2 * d
  + (-941084761547159090791333 / 1369595275155422342995968 : k) * a ^ 2 * b ^ 5 * d * g
  + (1406636827897586915813677037 / 175460372472689106830483456 : k) * a ^ 2 * b ^ 4 * c * d * f
  + (-186477446517077283139497 / 19022156599380865874944 : k) * a ^ 2 * b ^ 3 * d * f ^ 2
  + (538575 / 1327744 : k) * a ^ 2 * b ^ 2 * c ^ 3 * d ^ 2
  + (-237575 / 165968 : k) * a ^ 2 * b ^ 2 * c * d ^ 2 * g
  + (-228975 / 165968 : k) * a ^ 2 * b * c ^ 2 * d ^ 2 * f + (76325 / 20746 : k) * a ^ 2 * b * d ^ 2 * f * g
  + (-148217539479813251853480729 / 50131534992196887665852416 : k) * a * b ^ 6 * c ^ 3
  + (-15964966090082343775487 / 9948633959966748254208 : k) * a * b ^ 6 * c * g
  + (3641596060843811537602176927 / 175460372472689106830483456 : k) * a * b ^ 5 * c ^ 2 * f
  + (15964966090082343775487 / 5803369809980603148288 : k) * a * b ^ 5 * f * g
  + (-2041718110804502141325539895 / 43865093118172276707620864 : k) * a * b ^ 4 * c * f ^ 2
  + (59927097874622208195733959 / 10966273279543069176905216 : k) * a * b ^ 3 * c ^ 4 * d
  + (-789045565387316317141333627 / 49348229757943811296073472 : k) * a * b ^ 3 * c ^ 2 * d * g
  + (-767926722812712300669067 / 32099889261455211163968 : k) * a * b ^ 3 * d * g ^ 2
  + (160233843489124703342697 / 4755539149845216468736 : k) * a * b ^ 3 * f ^ 3
  + (-1902586675588715586910347 / 68113498630702293024256 : k) * a * b ^ 2 * c ^ 3 * d * f
  + (4407376383131032152628497875 / 49348229757943811296073472 : k) * a * b ^ 2 * c * d * f * g
  + (160233843489124703342697 / 4755539149845216468736 : k) * a * b * c ^ 2 * d * f ^ 2
  + (-53411281163041567780899 / 594442393730652058592 : k) * a * b * d * f ^ 2 * g
  + (9675 / 28864 : k) * a * c ^ 5 * d ^ 2 + (-16125 / 41492 : k) * a * c ^ 3 * d ^ 2 * g
  + (-13975 / 10373 : k) * a * c * d ^ 2 * g ^ 2
  + (2499781549972007251965 / 1810325545002054299648 : k) * b ^ 4 * c ^ 5
  + (-648744782492956030092913907 / 56397976866221498624083968 : k) * b ^ 4 * c ^ 3 * g
  + (-709924630645330306640845 / 18342793863688692093696 : k) * b ^ 4 * c * g ^ 2
  + (-34972325259539511890862987 / 6266441874024610958231552 : k) * b ^ 3 * c ^ 4 * f
  + (1357822697479463614657454143 / 22776106042127912905880064 : k) * b ^ 3 * c ^ 2 * f * g
  + (709924630645330306640845 / 10699963087151737054656 : k) * b ^ 3 * f * g ^ 2
  + (37778544936232218621 / 6857302306914515456 : k) * b ^ 2 * c ^ 3 * f ^ 2
  + (-131906475228771548681 / 1928616273819707472 : k) * b ^ 2 * c * f ^ 2 * g
  + (-1071334949988003107985 / 452581386250513574912 : k) * b * c ^ 6 * d
  + (856416634538430504557158247 / 32898819838629207530715648 : k) * b * c ^ 4 * d * g
  + (84899158320554906731990189 / 6168528719742976412009184 : k) * b * c ^ 2 * d * g ^ 2
  + (-709924630645330306640845 / 4012486157681901395496 : k) * b * d * g ^ 3
  + (37778544936232218621 / 6857302306914515456 : k) * c ^ 5 * d * f
  + (-640961535723782850587 / 7714465095278829888 : k) * c ^ 3 * d * f * g
  + (131906475228771548681 / 723231102682390302 : k) * c * d * f * g ^ 2

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #14: `BCDFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*d*f^2`, 63 cofactor terms. -/
theorem quarticCostChamberBCDFG14810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * muQuarticCostChamberBCDFG14Face810 a b c d e f g + xiQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * xiQuarticCostChamberBCDFG14Face810 a b c d e f g) +
      (piQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * piQuarticCostChamberBCDFG14Face810 a b c d e f g + kappaQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDFG14Face810 a b c d e f g)) +
      (n2QuarticCostChamberBCDFG14Cofactor810 a b c d e f g * n2QuarticCostChamberBCDFG14Face810 a b c d e f g)) =
      a * b * c ^ 2 * d * f ^ 2 := by
  have h1 : muQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * muQuarticCostChamberBCDFG14Face810 a b c d e f g + xiQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * xiQuarticCostChamberBCDFG14Face810 a b c d e f g = quarticCostChamberBCDFG14810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCDFG14Cofactor810, muQuarticCostChamberBCDFG14Face810, xiQuarticCostChamberBCDFG14Cofactor810, xiQuarticCostChamberBCDFG14Face810, quarticCostChamberBCDFG14810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * piQuarticCostChamberBCDFG14Face810 a b c d e f g + kappaQuarticCostChamberBCDFG14Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDFG14Face810 a b c d e f g = quarticCostChamberBCDFG14810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCDFG14Cofactor810, piQuarticCostChamberBCDFG14Face810, kappaQuarticCostChamberBCDFG14Cofactor810, kappaQuarticCostChamberBCDFG14Face810, quarticCostChamberBCDFG14810_identityPartial2]
    ring
  have h3 : n2QuarticCostChamberBCDFG14Cofactor810 a b c d e f g * n2QuarticCostChamberBCDFG14Face810 a b c d e f g = quarticCostChamberBCDFG14810_identityPartial3 a b c d e f g := by
    simp only [n2QuarticCostChamberBCDFG14Cofactor810, n2QuarticCostChamberBCDFG14Face810, quarticCostChamberBCDFG14810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCDFG14810_identityPartial1, quarticCostChamberBCDFG14810_identityPartial2, quarticCostChamberBCDFG14810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDFG14810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDFG14Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDFG14810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b * c ^ 2 * d * f ^ 2 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact (hb hRlll).elim
      ·
        exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRll)
    ·
      exact (hd hRl).elim
  ·
    exact hf ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 44 : k) * c * d

def xiQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a * b * c * d + (-4 : k) * a * d * f

def xiQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (2 / 11 : k) * b * c + (-4 / 11 : k) * f

def piQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (1 / 176 : k) * d

def kappaQuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * a * b * d

def n2QuarticCostChamberBCDFG15Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-12 : k) * c ^ 2 * d + 32 * d * g

def n2QuarticCostChamberBCDFG15Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 88 : k) * a * b ^ 2 + (1 / 22 : k) * c ^ 2 + (-2 / 11 : k) * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #15: `BCDFG` / `BF·BG·CF·CG·DD·BBB·BBC·BCC·CCC`, target `a*c*d^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCDFG15810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * muQuarticCostChamberBCDFG15Face810 a b c d e f g +
      xiQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * xiQuarticCostChamberBCDFG15Face810 a b c d e f g +
      piQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * piQuarticCostChamberBCDFG15Face810 a b c d e f g +
      kappaQuarticCostChamberBCDFG15Cofactor810 a b c d e f g * kappaQuarticCostChamberBCDFG15Face810 a b c d e f g +
      n2QuarticCostChamberBCDFG15Cofactor810 a b c d e f g * n2QuarticCostChamberBCDFG15Face810 a b c d e f g =
      a * c * d ^ 3 := by
  simp only [muQuarticCostChamberBCDFG15Face810, xiQuarticCostChamberBCDFG15Face810, piQuarticCostChamberBCDFG15Face810, kappaQuarticCostChamberBCDFG15Face810, n2QuarticCostChamberBCDFG15Face810, muQuarticCostChamberBCDFG15Cofactor810, xiQuarticCostChamberBCDFG15Cofactor810, piQuarticCostChamberBCDFG15Cofactor810, kappaQuarticCostChamberBCDFG15Cofactor810, n2QuarticCostChamberBCDFG15Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCDFG15810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCDFG15Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCDFG15810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * c * d ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      exact (ha hLl).elim
    ·
      exact (hc hRl).elim
  ·
    exact hd ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

def muQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (3355 / 26738688 : k) * a ^ 2 * b ^ 2 * e ^ 2 + (-3243 / 2524160 : k) * a * b ^ 4 * c ^ 2
  + (-8101727 / 5169479680 : k) * a * b ^ 4 * g + (15295246243 / 2047113953280 : k) * a * b ^ 3 * c * f
  + (168082576657 / 1023556976640 : k) * a * b ^ 2 * c ^ 2 * e
  + (826223179 / 171048960 : k) * a * b ^ 2 * e * g + (-5037198949 / 15508439040 : k) * a * b ^ 2 * f ^ 2
  + (20885338507 / 11631329280 : k) * a * b * c * e * f + (-3440779 / 969277440 : k) * a * c ^ 2 * e ^ 2
  + (3355 / 2506752 : k) * a * e ^ 2 * g + (3056583163 / 2907832320 : k) * a * e * f ^ 2
  + (3619 / 315520 : k) * b ^ 2 * c ^ 4 + (-471116407189 / 383833866240 : k) * b ^ 2 * c ^ 2 * g
  + (123902009651 / 4361748480 : k) * b ^ 2 * g ^ 2 + (-19597476089 / 52942602240 : k) * b * c ^ 3 * f
  + (3354466385617 / 191916933120 : k) * b * c * f * g + (-555698239729 / 255889244160 : k) * c ^ 4 * e
  + (-41618401021 / 5644615680 : k) * c ^ 2 * e * g + (2028874349603 / 383833866240 : k) * c ^ 2 * f ^ 2
  + (35233636591 / 1090437120 : k) * e * g ^ 2 + (78902895179 / 4361748480 : k) * f ^ 2 * g

def xiQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a * b ^ 4 + 12 * a * b ^ 2 * e + 36 * b ^ 2 * c ^ 2 + (-32 : k) * b ^ 2 * g
  + (-80 : k) * b * c * f + (-48 : k) * c ^ 2 * e + 128 * e * g + 64 * f ^ 2

def xiQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (-47 / 473280 : k) * a ^ 2 * b ^ 2 * c * e + (671 / 136839168 : k) * a ^ 2 * b * e * f
  + (17437 / 31236480 : k) * a * b ^ 2 * c ^ 3 + (-77161917331 / 63972311040 : k) * a * b ^ 2 * c * g
  + (-464640947137 / 767667732480 : k) * a * b * c ^ 2 * f + (31035626483 / 8723496960 : k) * a * b * f * g
  + (6395083 / 11631329280 : k) * a * c ^ 3 * e + (-3440779 / 1453916160 : k) * a * c * e * g
  + (10940393543 / 10662051840 : k) * a * c * f ^ 2 + (709022041 / 3308912640 : k) * c ^ 5
  + (-3847962433 / 8723496960 : k) * c ^ 3 * g + (-13344101641 / 1654456320 : k) * c * g ^ 2

def piQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

def piQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (-3337 / 13882880 : k) * a * b ^ 2 * c * e + (-202526273 / 6203375616 : k) * a * b * e * f
  + (5129 / 20193280 : k) * a * c * e ^ 2 + (3619 / 3786240 : k) * b ^ 2 * c ^ 3
  + (-11420781463 / 170592829440 : k) * b ^ 2 * c * g + (-171917281 / 7843348480 : k) * b * c ^ 2 * f
  + (207613 / 121159680 : k) * b * f * g + (11363801591 / 341185658880 : k) * c ^ 3 * e
  + (-60361 / 39198720 : k) * c * e * g + (-2029846219 / 34118565888 : k) * c * f ^ 2

def kappaQuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (1175 / 2776576 : k) * a ^ 2 * b ^ 3 * c * e + (607670075 / 6203375616 : k) * a ^ 2 * b ^ 2 * e * f
  + (68853 / 1292369920 : k) * a ^ 2 * b * c * e ^ 2 + (61061 / 64618496 : k) * a ^ 2 * e ^ 2 * f
  + (-162949 / 83297280 : k) * a * b ^ 3 * c ^ 3 + (-97198643093 / 28432138240 : k) * a * b ^ 3 * c * g
  + (-162910049687 / 93050634240 : k) * a * b ^ 2 * c ^ 2 * f
  + (62014938019 / 5815664640 : k) * a * b ^ 2 * f * g
  + (-98691076147 / 170592829440 : k) * a * b * c ^ 3 * e + (11375539 / 3554017280 : k) * a * b * c * e * g
  + (48914623711 / 11631329280 : k) * a * b * c * f ^ 2 + (4992579641 / 2584739840 : k) * a * c ^ 2 * e * f
  + (-994164581 / 193855488 : k) * a * e * f * g + (-4900982297 / 1938554880 : k) * a * f ^ 3
  + (709022041 / 1102970880 : k) * b * c ^ 5 + (-84224131 / 2907832320 : k) * b * c ^ 3 * g
  + (-549038006861 / 15993077760 : k) * b * c * g ^ 2 + (709022041 / 2205941760 : k) * c ^ 4 * f
  + (-4187533201 / 1599307776 : k) * c ^ 2 * f * g + (-207613 / 3786240 : k) * f * g ^ 2

def n4QuarticCostChamberBCEFG16Face810 (a b c d e f g : k) : k :=
  31 * a ^ 2 * b ^ 3 * c + (-44 : k) * a ^ 2 * b ^ 2 * f + (-24 : k) * a ^ 2 * b * c * e
  + 32 * a ^ 2 * e * f + (-96 : k) * a * b * c ^ 3 + 256 * a * b * c * g + 128 * a * c ^ 2 * f
  + (-1024 : k) * a * f * g

def n4QuarticCostChamberBCEFG16Cofactor810 (a b c d e f g : k) : k :=
  (47 / 315520 : k) * b ^ 3 * c ^ 2 + (352249 / 1938554880 : k) * b ^ 3 * g
  + (-6354407 / 7754219520 : k) * b ^ 2 * c * f + (-1007719 / 1292369920 : k) * b * c ^ 2 * e
  + (-61061 / 96927744 : k) * b * e * g + (3095833 / 1938554880 : k) * b * f ^ 2
  + (351207 / 323092480 : k) * c * e * f

def quarticCostChamberBCEFG16810_identityPartial1 (a b c d e f g : k) : k :=
  (47 / 157760 : k) * a ^ 3 * b ^ 6 * c * e + (-671 / 45613056 : k) * a ^ 3 * b ^ 5 * e * f
  + (-1053621 / 1292369920 : k) * a ^ 3 * b ^ 4 * c * e ^ 2
  + (-61061 / 64618496 : k) * a ^ 3 * b ^ 3 * e ^ 2 * f + (-460553 / 83297280 : k) * a ^ 2 * b ^ 6 * c ^ 3
  + (123298653535 / 34118565888 : k) * a ^ 2 * b ^ 6 * c * g
  + (222591418081 / 120418467840 : k) * a ^ 2 * b ^ 5 * c ^ 2 * f
  + (-61998337423 / 5815664640 : k) * a ^ 2 * b ^ 5 * f * g
  + (33717111157 / 68237131776 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e
  + (289479061 / 10662051840 : k) * a ^ 2 * b ^ 4 * c * e * g
  + (-2104689858629 / 511778488320 : k) * a ^ 2 * b ^ 4 * c * f ^ 2
  + (-2261718061 / 710803456 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f
  + (327102703 / 80773120 : k) * a ^ 2 * b ^ 3 * e * f * g
  + (5037198949 / 1938554880 : k) * a ^ 2 * b ^ 3 * f ^ 3
  + (68853 / 323092480 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e ^ 2
  + (-267195 / 8077312 : k) * a ^ 2 * b ^ 2 * c * e ^ 2 * g
  + (11676041467 / 10662051840 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2
  + (2274841 / 80773120 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 * f
  + (-61061 / 6057984 : k) * a ^ 2 * b * e ^ 2 * f * g + (-339607677 / 40386560 : k) * a ^ 2 * b * e * f ^ 3
  + (-3730764241 / 6397231104 : k) * a * b ^ 4 * c ^ 5
  + (-1466051934337 / 31986155520 : k) * a * b ^ 4 * c ^ 3 * g
  + (473278864285 / 3198615552 : k) * a * b ^ 4 * c * g ^ 2
  + (-737801275999 / 31986155520 : k) * a * b ^ 3 * c ^ 4 * f
  + (37127496487 / 121159680 : k) * a * b ^ 3 * c ^ 2 * f * g
  + (-61991087539 / 181739520 : k) * a * b ^ 3 * f * g ^ 2
  + (-32749901207 / 7108034560 : k) * a * b ^ 2 * c ^ 5 * e
  + (43677344041 / 2665512960 : k) * a * b ^ 2 * c ^ 3 * e * g
  + (397059414607 / 3763077120 : k) * a * b ^ 2 * c ^ 3 * f ^ 2
  + (44817853 / 111063040 : k) * a * b ^ 2 * c * e * g ^ 2
  + (-435901560757 / 888504320 : k) * a * b ^ 2 * c * f ^ 2 * g
  + (69657471787 / 1777008640 : k) * a * b * c ^ 4 * e * f
  + (-43850926109 / 333189120 : k) * a * b * c ^ 2 * e * f * g
  + (-153450584581 / 940769280 : k) * a * b * c ^ 2 * f ^ 3
  + (596391475 / 3028992 : k) * a * b * e * f * g ^ 2 + (1675541139 / 20193280 : k) * a * b * f ^ 3 * g
  + (-15387 / 1262080 : k) * a * c ^ 5 * e ^ 2 + (5129 / 78880 : k) * a * c ^ 3 * e ^ 2 * g
  + (-142398399563 / 2665512960 : k) * a * c ^ 3 * e * f ^ 2 + (-5129 / 19720 : k) * a * c * e ^ 2 * g ^ 2
  + (54918581011 / 333189120 : k) * a * c * e * f ^ 2 * g + (10940393543 / 166594560 : k) * a * c * f ^ 4
  + (20439345941 / 2665512960 : k) * b ^ 2 * c ^ 7 + (-558476238301 / 31986155520 : k) * b ^ 2 * c ^ 5 * g
  + (-1715846231533 / 3998269440 : k) * b ^ 2 * c ^ 3 * g ^ 2
  + (58330035125 / 49978368 : k) * b ^ 2 * c * g ^ 3 + (-69096525677 / 4411883520 : k) * b * c ^ 6 * f
  + (-371614953613 / 7996538880 : k) * b * c ^ 4 * f * g
  + (802695095723 / 666378240 : k) * b * c ^ 2 * f * g ^ 2 + (-11363801591 / 7108034560 : k) * c ^ 7 * e
  + (11462310743 / 1332756480 : k) * c ^ 5 * e * g + (-13979008657 / 1881538560 : k) * c ^ 5 * f ^ 2
  + (-3831715709 / 111063040 : k) * c ^ 3 * e * g ^ 2 + (1612395703 / 23519232 : k) * c ^ 3 * f ^ 2 * g
  + (60361 / 38280 : k) * c * e * g ^ 3 + (3480516733 / 55531520 : k) * c * f ^ 2 * g ^ 2

def quarticCostChamberBCEFG16810_identityPartial2 (a b c d e f g : k) : k :=
  (-47 / 157760 : k) * a ^ 3 * b ^ 6 * c * e + (671 / 45613056 : k) * a ^ 3 * b ^ 5 * e * f
  + (1053621 / 1292369920 : k) * a ^ 3 * b ^ 4 * c * e ^ 2
  + (61061 / 64618496 : k) * a ^ 3 * b ^ 3 * e ^ 2 * f + (893 / 979968 : k) * a ^ 2 * b ^ 6 * c ^ 3
  + (-205818067649 / 56864276480 : k) * a ^ 2 * b ^ 6 * c * g
  + (-3718632324137 / 2047113953280 : k) * a ^ 2 * b ^ 5 * c ^ 2 * f
  + (62044834291 / 5815664640 : k) * a ^ 2 * b ^ 5 * f * g
  + (-159118627457 / 341185658880 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e
  + (-11588061 / 3554017280 : k) * a ^ 2 * b ^ 4 * c * e * g
  + (2060900363429 / 511778488320 : k) * a ^ 2 * b ^ 4 * c * f ^ 2
  + (5490027593 / 1777008640 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f
  + (-197886763 / 48463872 : k) * a ^ 2 * b ^ 3 * e * f * g
  + (-4900982297 / 1938554880 : k) * a ^ 2 * b ^ 3 * f ^ 3
  + (-6115167 / 323092480 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e ^ 2
  + (145073 / 8077312 : k) * a ^ 2 * b ^ 2 * c * e ^ 2 * g
  + (-3492615013 / 3554017280 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2
  + (1847839 / 80773120 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 * f
  + (61061 / 2019328 : k) * a ^ 2 * b * e ^ 2 * f * g + (202526273 / 24231936 : k) * a ^ 2 * b * e * f ^ 3
  + (-351207 / 10096640 : k) * a ^ 2 * c * e ^ 2 * f ^ 2
  + (19111229717 / 31986155520 : k) * a * b ^ 4 * c ^ 5
  + (1465390140721 / 31986155520 : k) * a * b ^ 4 * c ^ 3 * g
  + (-2367138271313 / 15993077760 : k) * a * b ^ 4 * c * g ^ 2
  + (734675052811 / 31986155520 : k) * a * b ^ 3 * c ^ 4 * f
  + (-37086415699 / 121159680 : k) * a * b ^ 3 * c ^ 2 * f * g
  + (62024903443 / 181739520 : k) * a * b ^ 3 * f * g ^ 2
  + (6443565115 / 1421606912 : k) * a * b ^ 2 * c ^ 5 * e
  + (-43306469449 / 2665512960 : k) * a * b ^ 2 * c ^ 3 * e * g
  + (-6733492195583 / 63972311040 : k) * a * b ^ 2 * c ^ 3 * f ^ 2
  + (-80719879 / 333189120 : k) * a * b ^ 2 * c * e * g ^ 2
  + (434792732597 / 888504320 : k) * a * b ^ 2 * c * f ^ 2 * g
  + (-69294675947 / 1777008640 : k) * a * b * c ^ 4 * e * f
  + (2923481707 / 22212608 : k) * a * b * c ^ 2 * e * f * g
  + (2605390738229 / 15993077760 : k) * a * b * c ^ 2 * f ^ 3
  + (-598345427 / 3028992 : k) * a * b * e * f * g ^ 2 + (-4927556761 / 60579840 : k) * a * b * f ^ 3 * g
  + (15387 / 1262080 : k) * a * c ^ 5 * e ^ 2 + (-5129 / 78880 : k) * a * c ^ 3 * e ^ 2 * g
  + (142027524971 / 2665512960 : k) * a * c ^ 3 * e * f ^ 2 + (5129 / 19720 : k) * a * c * e ^ 2 * g ^ 2
  + (-54547706419 / 333189120 : k) * a * c * e * f ^ 2 * g + (-10940393543 / 166594560 : k) * a * c * f ^ 4
  + (-20439345941 / 2665512960 : k) * b ^ 2 * c ^ 7 + (558476238301 / 31986155520 : k) * b ^ 2 * c ^ 5 * g
  + (1715846231533 / 3998269440 : k) * b ^ 2 * c ^ 3 * g ^ 2
  + (-58330035125 / 49978368 : k) * b ^ 2 * c * g ^ 3 + (69096525677 / 4411883520 : k) * b * c ^ 6 * f
  + (371614953613 / 7996538880 : k) * b * c ^ 4 * f * g
  + (-802695095723 / 666378240 : k) * b * c ^ 2 * f * g ^ 2 + (11363801591 / 7108034560 : k) * c ^ 7 * e
  + (-11462310743 / 1332756480 : k) * c ^ 5 * e * g + (13979008657 / 1881538560 : k) * c ^ 5 * f ^ 2
  + (3831715709 / 111063040 : k) * c ^ 3 * e * g ^ 2 + (-1612395703 / 23519232 : k) * c ^ 3 * f ^ 2 * g
  + (-60361 / 38280 : k) * c * e * g ^ 3 + (-3480516733 / 55531520 : k) * c * f ^ 2 * g ^ 2

def quarticCostChamberBCEFG16810_identityPartial3 (a b c d e f g : k) : k :=
  (1457 / 315520 : k) * a ^ 2 * b ^ 6 * c ^ 3 + (10919719 / 1938554880 : k) * a ^ 2 * b ^ 6 * c * g
  + (-1709033 / 53477376 : k) * a ^ 2 * b ^ 5 * c ^ 2 * f
  + (-3874739 / 484638720 : k) * a ^ 2 * b ^ 5 * f * g
  + (-35859577 / 1292369920 : k) * a ^ 2 * b ^ 4 * c ^ 3 * e
  + (-11577949 / 484638720 : k) * a ^ 2 * b ^ 4 * c * e * g
  + (8293465 / 96927744 : k) * a ^ 2 * b ^ 4 * c * f ^ 2
  + (29866829 / 323092480 : k) * a ^ 2 * b ^ 3 * c ^ 2 * e * f
  + (4062853 / 121159680 : k) * a ^ 2 * b ^ 3 * e * f * g
  + (-34054163 / 484638720 : k) * a ^ 2 * b ^ 3 * f ^ 3
  + (3023157 / 161546240 : k) * a ^ 2 * b ^ 2 * c ^ 3 * e ^ 2
  + (61061 / 4038656 : k) * a ^ 2 * b ^ 2 * c * e ^ 2 * g
  + (-27231737 / 242319360 : k) * a ^ 2 * b ^ 2 * c * e * f ^ 2
  + (-103067 / 2019328 : k) * a ^ 2 * b * c ^ 2 * e ^ 2 * f
  + (-61061 / 3028992 : k) * a ^ 2 * b * e ^ 2 * f * g + (3095833 / 60579840 : k) * a ^ 2 * b * e * f ^ 3
  + (351207 / 10096640 : k) * a ^ 2 * c * e ^ 2 * f ^ 2 + (-141 / 9860 : k) * a * b ^ 4 * c ^ 5
  + (417799 / 20193280 : k) * a * b ^ 4 * c ^ 3 * g + (352249 / 7572480 : k) * a * b ^ 4 * c * g ^ 2
  + (7894503 / 80773120 : k) * a * b ^ 3 * c ^ 4 * f + (-3423399 / 10096640 : k) * a * b ^ 3 * c ^ 2 * f * g
  + (-352249 / 1893120 : k) * a * b ^ 3 * f * g ^ 2 + (3023157 / 40386560 : k) * a * b ^ 2 * c ^ 5 * e
  + (-351207 / 2524160 : k) * a * b ^ 2 * c ^ 3 * e * g
  + (-7820953 / 30289920 : k) * a * b ^ 2 * c ^ 3 * f ^ 2
  + (-61061 / 378624 : k) * a * b ^ 2 * c * e * g ^ 2 + (2461 / 1972 : k) * a * b ^ 2 * c * f ^ 2 * g
  + (-103067 / 504832 : k) * a * b * c ^ 4 * e * f + (3771473 / 3786240 : k) * a * b * c ^ 2 * e * f * g
  + (3095833 / 15144960 : k) * a * b * c ^ 2 * f ^ 3 + (61061 / 94656 : k) * a * b * e * f * g ^ 2
  + (-3095833 / 1893120 : k) * a * b * f ^ 3 * g + (351207 / 2524160 : k) * a * c ^ 3 * e * f ^ 2
  + (-351207 / 315520 : k) * a * c * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #16: `BCEFG` / `BF·BG·CF·CG·BBB·BBC·BCC·CCC`, target `a*b*c^2*e*f*g`, 70 cofactor terms. -/
theorem quarticCostChamberBCEFG16810_identity
    (a b c d e f g : k) :
    (((muQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * muQuarticCostChamberBCEFG16Face810 a b c d e f g + xiQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * xiQuarticCostChamberBCEFG16Face810 a b c d e f g) +
      (piQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * piQuarticCostChamberBCEFG16Face810 a b c d e f g + kappaQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * kappaQuarticCostChamberBCEFG16Face810 a b c d e f g)) +
      (n4QuarticCostChamberBCEFG16Cofactor810 a b c d e f g * n4QuarticCostChamberBCEFG16Face810 a b c d e f g)) =
      a * b * c ^ 2 * e * f * g := by
  have h1 : muQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * muQuarticCostChamberBCEFG16Face810 a b c d e f g + xiQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * xiQuarticCostChamberBCEFG16Face810 a b c d e f g = quarticCostChamberBCEFG16810_identityPartial1 a b c d e f g := by
    simp only [muQuarticCostChamberBCEFG16Cofactor810, muQuarticCostChamberBCEFG16Face810, xiQuarticCostChamberBCEFG16Cofactor810, xiQuarticCostChamberBCEFG16Face810, quarticCostChamberBCEFG16810_identityPartial1]
    ring
  have h2 : piQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * piQuarticCostChamberBCEFG16Face810 a b c d e f g + kappaQuarticCostChamberBCEFG16Cofactor810 a b c d e f g * kappaQuarticCostChamberBCEFG16Face810 a b c d e f g = quarticCostChamberBCEFG16810_identityPartial2 a b c d e f g := by
    simp only [piQuarticCostChamberBCEFG16Cofactor810, piQuarticCostChamberBCEFG16Face810, kappaQuarticCostChamberBCEFG16Cofactor810, kappaQuarticCostChamberBCEFG16Face810, quarticCostChamberBCEFG16810_identityPartial2]
    ring
  have h3 : n4QuarticCostChamberBCEFG16Cofactor810 a b c d e f g * n4QuarticCostChamberBCEFG16Face810 a b c d e f g = quarticCostChamberBCEFG16810_identityPartial3 a b c d e f g := by
    simp only [n4QuarticCostChamberBCEFG16Cofactor810, n4QuarticCostChamberBCEFG16Face810, quarticCostChamberBCEFG16810_identityPartial3]
    ring
  rw [h1, h2, h3]
  simp only [quarticCostChamberBCEFG16810_identityPartial1, quarticCostChamberBCEFG16810_identityPartial2, quarticCostChamberBCEFG16810_identityPartial3]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCEFG16810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (hn4 : n4QuarticCostChamberBCEFG16Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCEFG16810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn4] at hid
  have hz : a * b * c ^ 2 * e * f * g = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          rcases (mul_eq_zero.mp hLlll) with hLllll | hRllll
          ·
            exact (ha hLllll).elim
          ·
            exact (hb hRllll).elim
        ·
          exact hc ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRlll)
      ·
        exact (he hRll).elim
    ·
      exact (hf hRl).elim
  ·
    exact (hg hR).elim

def muQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g + 16 * e ^ 2

def muQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (3 / 176 : k) * c * e

def xiQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-12 : k) * c ^ 2 * e + 32 * e * g

def xiQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (1 / 352 : k) * a * b ^ 2 + (-1 / 88 : k) * c ^ 2 + (1 / 22 : k) * g

def piQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2 + 1024 * g ^ 2

def piQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 704 : k) * e

def kappaQuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

def kappaQuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (-3 / 704 : k) * a * b * e

def n2QuarticCostChamberBCEFG17Face810 (a b c d e f g : k) : k :=
  (-3 : k) * b * c * e + 4 * e * f

def n2QuarticCostChamberBCEFG17Cofactor810 (a b c d e f g : k) : k :=
  (1 / 22 : k) * a * b * c + (-1 / 11 : k) * a * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #17: `BCEFG` / `BF·BG·CF·CG·EE·BBB·BBC·BCC·CCC`, target `c*e^3`, 8 cofactor terms. -/
theorem quarticCostChamberBCEFG17810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * muQuarticCostChamberBCEFG17Face810 a b c d e f g +
      xiQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * xiQuarticCostChamberBCEFG17Face810 a b c d e f g +
      piQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * piQuarticCostChamberBCEFG17Face810 a b c d e f g +
      kappaQuarticCostChamberBCEFG17Cofactor810 a b c d e f g * kappaQuarticCostChamberBCEFG17Face810 a b c d e f g +
      n2QuarticCostChamberBCEFG17Cofactor810 a b c d e f g * n2QuarticCostChamberBCEFG17Face810 a b c d e f g =
      c * e ^ 3 := by
  simp only [muQuarticCostChamberBCEFG17Face810, xiQuarticCostChamberBCEFG17Face810, piQuarticCostChamberBCEFG17Face810, kappaQuarticCostChamberBCEFG17Face810, n2QuarticCostChamberBCEFG17Face810, muQuarticCostChamberBCEFG17Cofactor810, xiQuarticCostChamberBCEFG17Cofactor810, piQuarticCostChamberBCEFG17Cofactor810, kappaQuarticCostChamberBCEFG17Cofactor810, n2QuarticCostChamberBCEFG17Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBCEFG17810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBCEFG17Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBCEFG17810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : c * e ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    exact (hc hL).elim
  ·
    exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

def muQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * b * f - a * d ^ 2 + 4 * e ^ 2

def muQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (1 / 256 : k) * a * b ^ 4 + (1 / 24 : k) * b ^ 2 * g + (-1 / 3 : k) * f ^ 2

def xiQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + (-8 : k) * a * d * f + 32 * e * g

def xiQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 192 : k) * b ^ 2 * e + (1 / 24 : k) * d * f

def piQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + 64 * a * b ^ 2 * g + 256 * a * b * d * e + (-256 : k) * a * f ^ 2 + 1024 * g ^ 2

def piQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (1 / 384 : k) * b * f

def kappaQuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  a * b ^ 3 + 32 * b * g + 32 * d * e

def kappaQuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 12 : k) * f * g

def n2QuarticCostChamberBDEFG18Face810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + 32 * d * g + 32 * e * f

def n2QuarticCostChamberBDEFG18Cofactor810 (a b c d e f g : k) : k :=
  (1 / 768 : k) * a * b ^ 2 * d + (1 / 24 : k) * e * f

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #18: `BDEFG` / `BF·BG·DD·DE·EE·BBB`, target `a*b^2*d*e*f`, 9 cofactor terms. -/
theorem quarticCostChamberBDEFG18810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * muQuarticCostChamberBDEFG18Face810 a b c d e f g +
      xiQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * xiQuarticCostChamberBDEFG18Face810 a b c d e f g +
      piQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * piQuarticCostChamberBDEFG18Face810 a b c d e f g +
      kappaQuarticCostChamberBDEFG18Cofactor810 a b c d e f g * kappaQuarticCostChamberBDEFG18Face810 a b c d e f g +
      n2QuarticCostChamberBDEFG18Cofactor810 a b c d e f g * n2QuarticCostChamberBDEFG18Face810 a b c d e f g =
      a * b ^ 2 * d * e * f := by
  simp only [muQuarticCostChamberBDEFG18Face810, xiQuarticCostChamberBDEFG18Face810, piQuarticCostChamberBDEFG18Face810, kappaQuarticCostChamberBDEFG18Face810, n2QuarticCostChamberBDEFG18Face810, muQuarticCostChamberBDEFG18Cofactor810, xiQuarticCostChamberBDEFG18Cofactor810, piQuarticCostChamberBDEFG18Cofactor810, kappaQuarticCostChamberBDEFG18Cofactor810, n2QuarticCostChamberBDEFG18Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberBDEFG18810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (hn2 : n2QuarticCostChamberBDEFG18Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberBDEFG18810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn2] at hid
  have hz : a * b ^ 2 * d * e * f = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        rcases (mul_eq_zero.mp hLll) with hLlll | hRlll
        ·
          exact (ha hLlll).elim
        ·
          exact hb ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hRlll)
      ·
        exact (hd hRll).elim
    ·
      exact (he hRl).elim
  ·
    exact (hf hR).elim

def muQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  -a * d ^ 2 - c ^ 3 + 8 * c * g + 4 * e ^ 2

def muQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (-1 / 12 : k) * a ^ 2 * f * g

def xiQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  (-2 : k) * a * d * f + (-3 : k) * c ^ 2 * e + 8 * e * g

def xiQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (-7 / 192 : k) * a ^ 2 * c ^ 2 * d + (1 / 4 : k) * a ^ 2 * d * g + (7 / 24 : k) * a ^ 2 * e * f

def piQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  8 * a * c * d ^ 2 + (-16 : k) * a * f ^ 2 + 3 * c ^ 4 + (-16 : k) * c ^ 2 * g + (-32 : k) * c * e ^ 2
  + 64 * g ^ 2

def piQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (1 / 96 : k) * a ^ 2 * c * f

def kappaQuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  c * f + d * e

def kappaQuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (1 / 6 : k) * a ^ 3 * f ^ 2 + (-1 / 32 : k) * a ^ 2 * c ^ 4 + (1 / 12 : k) * a ^ 2 * c ^ 2 * g
  + a ^ 2 * c * e ^ 2

def n4QuarticCostChamberCDEFG19Face810 (a b c d e f g : k) : k :=
  (-3 : k) * a ^ 2 * c ^ 2 * d + 8 * a ^ 2 * d * g + 8 * a ^ 2 * e * f

def n4QuarticCostChamberCDEFG19Cofactor810 (a b c d e f g : k) : k :=
  (5 / 96 : k) * a * d * f + (5 / 192 : k) * c ^ 2 * e + (-1 / 4 : k) * e * g

set_option maxHeartbeats 64000000 in
/-- Deep-rescue #19: `CDEFG` / `CF·CG·DD·DE·EE·CCC`, target `a^2*c*d*e^3`, 12 cofactor terms. -/
theorem quarticCostChamberCDEFG19810_identity
    (a b c d e f g : k) :
    muQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * muQuarticCostChamberCDEFG19Face810 a b c d e f g +
      xiQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * xiQuarticCostChamberCDEFG19Face810 a b c d e f g +
      piQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * piQuarticCostChamberCDEFG19Face810 a b c d e f g +
      kappaQuarticCostChamberCDEFG19Cofactor810 a b c d e f g * kappaQuarticCostChamberCDEFG19Face810 a b c d e f g +
      n4QuarticCostChamberCDEFG19Cofactor810 a b c d e f g * n4QuarticCostChamberCDEFG19Face810 a b c d e f g =
      a ^ 2 * c * d * e ^ 3 := by
  simp only [muQuarticCostChamberCDEFG19Face810, xiQuarticCostChamberCDEFG19Face810, piQuarticCostChamberCDEFG19Face810, kappaQuarticCostChamberCDEFG19Face810, n4QuarticCostChamberCDEFG19Face810, muQuarticCostChamberCDEFG19Cofactor810, xiQuarticCostChamberCDEFG19Cofactor810, piQuarticCostChamberCDEFG19Cofactor810, kappaQuarticCostChamberCDEFG19Cofactor810, n4QuarticCostChamberCDEFG19Cofactor810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCostChamberCDEFG19810_impossible
    (a b c d e f g : k)
    (hmu : muQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hxi : xiQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hpi : piQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hkappa : kappaQuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (hn4 : n4QuarticCostChamberCDEFG19Face810 a b c d e f g = 0)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hd : d ≠ 0)
    (he : e ≠ 0)
    (hf : f ≠ 0)
    (hg : g ≠ 0) :
    False := by
  have hid := quarticCostChamberCDEFG19810_identity a b c d e f g
  rw [hmu, hxi, hpi, hkappa, hn4] at hid
  have hz : a ^ 2 * c * d * e ^ 3 = 0 := by
    simpa using hid.symm
  rcases (mul_eq_zero.mp hz) with hL | hR
  ·
    rcases (mul_eq_zero.mp hL) with hLl | hRl
    ·
      rcases (mul_eq_zero.mp hLl) with hLll | hRll
      ·
        exact ha ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hLll)
      ·
        exact (hc hRll).elim
    ·
      exact (hd hRl).elim
  ·
    exact he ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hR)

end QuarticRescueCertificates810

/-! ## Family (c) — `N₇` column kills (202 walls)

On a weak-band wall the pure-`A` `π`-column of `N₇` sits three
`A`'s above `κ`'s.  If every other monomial of `N₇` has degree
strictly below that column, the column is the unique top and
forces the load to vanish.  Shape of `quarticSigma_<load>_eq_zero`
with carrier `N₇` and the rest bound as the wall hypothesis.
-/

section QuarticN7ColumnKills810

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `l`: the pure-`A` column `(6435/268435456) · l · A^8` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_l_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hrest : rest.natDegree < 8 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticLTowerFace810 l A + rest) :
    l = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (6435 / 268435456 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticLTowerFace810 l A).natDegree = 8 * A.natDegree := by
    simp only [n7QuarticLTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `beta`: the pure-`A` column `(429/4194304) · beta · A^7` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_beta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hrest : rest.natDegree < 7 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticBetaTowerFace810 beta A + rest) :
    beta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (429 / 4194304 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticBetaTowerFace810 beta A).natDegree = 7 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `delta`: the pure-`A` column `(231/524288) · delta · A^6` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_delta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hrest : rest.natDegree < 6 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticDeltaTowerFace810 delta A + rest) :
    delta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (231 / 524288 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticDeltaTowerFace810 delta A).natDegree = 6 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  subst hbeta
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `zeta`: the pure-`A` column `(63/32768) · zeta · A^5` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_zeta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hdelta : delta = 0)
    (hrest : rest.natDegree < 5 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticZetaTowerFace810 zeta A + rest) :
    zeta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (63 / 32768 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticZetaTowerFace810 zeta A).natDegree = 5 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  subst hbeta
  subst hdelta
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `theta`: the pure-`A` column `(35/4096) · theta · A^4` is the unique top. The split `N₇ = face + rest` is a hypothesis (the module identity unfolds `Π` and lives in the residual assembly). -/
theorem quarticSigma_theta_eq_zero_of_N7_column
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G rest : k[X])
    (hApos : 0 < A.natDegree)
    (hl : l = 0)
    (hbeta : beta = 0)
    (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hrest : rest.natDegree < 4 * A.natDegree)
    (hN7 : (degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree ≤ 3 * A.natDegree)
    (heq : degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G =
        n7QuarticThetaTowerFace810 theta A + rest) :
    theta = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (35 / 4096 * theta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n7QuarticThetaTowerFace810 theta A).natDegree = 4 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  subst hl
  subst hbeta
  subst hdelta
  subst hzeta
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]),
    hlead] at hN7
  omega

end QuarticN7ColumnKills810

/-! ## Family (c) — empty walls (101)

`w_π · n_A = c₀(Φ)` is infeasible on the chamber in the
`(n_A,…,n_G)` arena (with `n_X ≥ 0` and `0 < n_A`).  Closed by
`omega` from the chamber conjuncts.
-/

section QuarticEmptyWalls810

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCD` / `DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCD6_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCD6810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCD6810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `CG·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG16_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG16810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `CG·DD`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG17_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG17810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG17810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG18_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG18810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG18810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDG` / `DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDG24_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDG24810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDG24810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDFG7_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BEFG7_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCEFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEG30_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEG30810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEG30810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEG` / `CG·DD·CCC`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEG30_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEG30810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEG30810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDFG10_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG10_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG14_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG14_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG45_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDFG45_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDFG54_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG54810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG54810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDFG` / `CG·DD·CCC`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDFG54_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDFG54810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDFG54810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCEFG10_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG10_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCEFG14_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG14_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG14810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG14810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCEFG45_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCEFG45_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCEFG45810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCEFG45810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG7_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BDEFG7_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG7_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG7810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG13_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG13_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BDEFG39_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG39810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG39810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BDEFG39_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBDEFG39810 A B C D E F G)
    (hw : 4 * D.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBDEFG39810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG7_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_CDEFG7_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG7810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG7810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG10810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG13_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG13810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `CDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_CDEFG39_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberCDEFG39810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberCDEFG39810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG10_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG10_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG10_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG10_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `omicron`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG10_omicron_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `omicron`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG10_omicron_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG10810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG10810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG13_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG13_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG13_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·DD·DF·DG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG13_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG13810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG13810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG16_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG16_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG16_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·CF·CG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG16_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG16810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG16810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG20_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG20_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG20_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG20_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG20810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG20810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG23_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG23810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG23810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG23_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG23810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG23810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG26_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG26810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG26810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `BF·BG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG26_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG26810 A B C D E F G)
    (hw : 2 * B.natDegree + 2 * F.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG26810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG81_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG81_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG81_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `nu`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG81_nu_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG81810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG81810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG84_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG84810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG84810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·DD·DF·DG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG84_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG84810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG84810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG87_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG87810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG87810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CF·CG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG87_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG87810 A B C D E F G)
    (hw : C.natDegree + F.natDegree = 2 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG87810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CG·DD·CCC`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG102_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG102810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG102810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `CG·DD·CCC`, carrier `nu`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG102_nu_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG102810 A B C D E F G)
    (hw : 2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG102810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `theta`. -/
theorem quarticWallEmpty_BCDEFG115_kappa_Theta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG115810 A B C D E F G)
    (hw : 4 * D.natDegree = A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG115810, QuarticRatioConeA810] at hc hw
  omega

set_option maxHeartbeats 64000000 in
/-- Empty wall: `BCDEFG` / `DD·DE·DF·DG·EE·EF·EG·FF·FG·GG`, carrier `kappa`, load `zeta`. -/
theorem quarticWallEmpty_BCDEFG115_kappa_Zeta810
    (A B C D E F G : k[X])
    (hc : QuarticChamberBCDEFG115810 A B C D E F G)
    (hw : 4 * D.natDegree = 3 * A.natDegree) :
    False := by
  simp only [QuarticChamberBCDEFG115810, QuarticRatioConeA810] at hc hw
  omega

end QuarticEmptyWalls810

/-! ## Family (c) — `p`-augmented split walls (102), nine patterns

Pivots are the five `omega`-friendly comparisons
`cost(DG), cost(CCD), cost(DDD), cost(CDG), cost(CCCD) ⋚ w_π·a`.
On each sub-cell the even faces `μ, ξ, π` stay clean and every odd
form enters as a `p`-augmented row.  The scalar identity of each
pattern is the torus-saturating combination (live letters and `a`
inverted, `p` not inverted).
-/

section QuarticWallSplit810

/-- Pattern 1: pivots `nu:CCD, omicron:DDD` (11 walls, 5 sub-cells). -/
def quarticWallSplitPattern1810Pivots : Prop := True

/-- `cost(CCD)` versus `w * A.natDegree`. -/
def quarticCost_CCD_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree < 4 * C.natDegree + 2 * D.natDegree + w * A.natDegree

def quarticCost_CCD_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree = 4 * C.natDegree + 2 * D.natDegree + w * A.natDegree

def quarticCost_CCD_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree > 4 * C.natDegree + 2 * D.natDegree + w * A.natDegree

/-- `cost(DDD)` versus `w * A.natDegree`. -/
def quarticCost_DDD_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  15 * A.natDegree < 6 * D.natDegree + w * A.natDegree

def quarticCost_DDD_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  15 * A.natDegree = 6 * D.natDegree + w * A.natDegree

def quarticCost_DDD_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  15 * A.natDegree > 6 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticCost_CCD_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_CCD_lt_wall w A B C D E F G ∨
      quarticCost_CCD_eq_wall w A B C D E F G ∨
      quarticCost_CCD_gt_wall w A B C D E F G := by
  simp only [quarticCost_CCD_lt_wall, quarticCost_CCD_eq_wall, quarticCost_CCD_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
theorem quarticCost_DDD_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_DDD_lt_wall w A B C D E F G ∨
      quarticCost_DDD_eq_wall w A B C D E F G ∨
      quarticCost_DDD_gt_wall w A B C D E F G := by
  simp only [quarticCost_DDD_lt_wall, quarticCost_DDD_eq_wall, quarticCost_DDD_gt_wall]
  omega

/-- Split wall `BCD` / `DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_0_BCD_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

/-- Split wall `BCD` / `DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_1_BCD_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

/-- Split wall `BCD` / `DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_2_BCD_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

/-- Split wall `CDE` / `DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_3_CDE_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

/-- Split wall `CDE` / `DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_4_CDE_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

/-- Split wall `CDE` / `DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_5_CDE_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

/-- Split wall `CDE` / `DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_6_CDE_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

/-- Split wall `CDF` / `DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_7_CDF_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

/-- Split wall `CDF` / `DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_8_CDF_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

/-- Split wall `CDF` / `DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_9_CDF_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

/-- Split wall `CDF` / `DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 1. -/
def quarticWallSplit1_10_CDF_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

/-- Pattern 2: pivots `nu:CCD` (2 walls, 3 sub-cells). -/
def quarticWallSplitPattern2810Pivots : Prop := True

/-- Split wall `CDE` / `DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 2. -/
def quarticWallSplit2_0_CDE_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

/-- Split wall `CDF` / `DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 2. -/
def quarticWallSplit2_1_CDF_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

/-- Pattern 3: pivots `n6:CDG, nu:DG, omicron:DDD` (11 walls, 7 sub-cells). -/
def quarticWallSplitPattern3810Pivots : Prop := True

/-- `cost(CDG)` versus `w * A.natDegree`. -/
def quarticCost_CDG_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree < 2 * C.natDegree + 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

def quarticCost_CDG_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree = 2 * C.natDegree + 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

def quarticCost_CDG_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree > 2 * C.natDegree + 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

/-- `cost(DG)` versus `w * A.natDegree`. -/
def quarticCost_DG_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree < 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

def quarticCost_DG_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree = 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

def quarticCost_DG_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  13 * A.natDegree > 2 * D.natDegree + 2 * G.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticCost_CDG_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_CDG_lt_wall w A B C D E F G ∨
      quarticCost_CDG_eq_wall w A B C D E F G ∨
      quarticCost_CDG_gt_wall w A B C D E F G := by
  simp only [quarticCost_CDG_lt_wall, quarticCost_CDG_eq_wall, quarticCost_CDG_gt_wall]
  omega

set_option maxHeartbeats 64000000 in
theorem quarticCost_DG_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_DG_lt_wall w A B C D E F G ∨
      quarticCost_DG_eq_wall w A B C D E F G ∨
      quarticCost_DG_gt_wall w A B C D E F G := by
  simp only [quarticCost_DG_lt_wall, quarticCost_DG_eq_wall, quarticCost_DG_gt_wall]
  omega

/-- Split wall `BCDG` / `CG·CCC`, load `beta` (w=3), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDG` / `CG·CCC`, load `delta` (w=5), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDG` / `CG·CCC`, load `l` (w=1), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEG` / `CG·CCC`, load `beta` (w=3), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDEG` / `CG·CCC`, load `delta` (w=5), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDEG` / `CG·CCC`, load `l` (w=1), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEG` / `CG·CCC`, load `zeta` (w=7), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Split wall `CDFG` / `CG·CCC`, load `beta` (w=3), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDFG` / `CG·CCC`, load `delta` (w=5), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDFG` / `CG·CCC`, load `l` (w=1), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDFG` / `CG·CCC`, load `zeta` (w=7), 7 sub-cells, pattern 3. -/
def quarticWallSplit3_10_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Pattern 4: pivots `n6:CCCD, nu:CCD, nu:DG, omicron:DDD` (12 walls, 9 sub-cells). -/
def quarticWallSplitPattern4810Pivots : Prop := True

/-- `cost(CCCD)` versus `w * A.natDegree`. -/
def quarticCost_CCCD_lt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree < 6 * C.natDegree + 2 * D.natDegree + w * A.natDegree

def quarticCost_CCCD_eq_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree = 6 * C.natDegree + 2 * D.natDegree + w * A.natDegree

def quarticCost_CCCD_gt_wall (w : ℕ) (A B C D E F G : k[X]) : Prop :=
  17 * A.natDegree > 6 * C.natDegree + 2 * D.natDegree + w * A.natDegree

set_option maxHeartbeats 64000000 in
theorem quarticCost_CCCD_wall_trichotomy
    (w : ℕ) (A B C D E F G : k[X]) :
    quarticCost_CCCD_lt_wall w A B C D E F G ∨
      quarticCost_CCCD_eq_wall w A B C D E F G ∨
      quarticCost_CCCD_gt_wall w A B C D E F G := by
  simp only [quarticCost_CCCD_lt_wall, quarticCost_CCCD_eq_wall, quarticCost_CCCD_gt_wall]
  omega

/-- Split wall `BCDG` / `CG·DD`, load `beta` (w=3), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDG` / `CG·DD`, load `delta` (w=5), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDG` / `CG·DD`, load `l` (w=1), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEG` / `CG·DD`, load `beta` (w=3), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDEG` / `CG·DD`, load `delta` (w=5), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDEG` / `CG·DD`, load `l` (w=1), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEG` / `CG·DD`, load `zeta` (w=7), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Split wall `CDFG` / `CG·DD`, load `beta` (w=3), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDFG` / `CG·DD`, load `delta` (w=5), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDFG` / `CG·DD`, load `l` (w=1), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDFG` / `CG·DD`, load `theta` (w=9), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_10_CDFG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

/-- Split wall `CDFG` / `CG·DD`, load `zeta` (w=7), 9 sub-cells, pattern 4. -/
def quarticWallSplit4_11_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Pattern 5: pivots `nu:DG, omicron:DDD` (49 walls, 5 sub-cells). -/
def quarticWallSplitPattern5810Pivots : Prop := True

/-- Split wall `BCDG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Split wall `CDFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDFG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_10_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_11_BCDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_12_BCDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_13_BCDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_14_BCDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_15_BCDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_16_BCDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_17_BCDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_18_BCDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_19_BCDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_20_BCDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_21_BCDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_22_BCDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_23_BCDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_24_BCDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_25_BCDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_26_CDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_27_CDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_28_CDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_29_CDEFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_30_CDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_31_CDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_32_CDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `CDEFG` / `CG·DD·CCC`, load `zeta` (w=7), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_33_CDEFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 5 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_34_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_35_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_36_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_37_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_38_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_39_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_40_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_41_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_42_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_43_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_44_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_45_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `beta` (w=3), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_46_BCDEFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 9 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `delta` (w=5), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_47_BCDEFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 7 * A.natDegree

/-- Split wall `BCDEFG` / `CG·DD·CCC`, load `l` (w=1), 5 sub-cells, pattern 5. -/
def quarticWallSplit5_48_BCDEFG_L810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 11 * A.natDegree

/-- Pattern 6: pivots `n6:CDG, nu:CCD, nu:DG, omicron:DDD` (11 walls, 13 sub-cells). -/
def quarticWallSplitPattern6810Pivots : Prop := True

/-- Split wall `BCDG` / `DD·CCC`, load `beta` (w=3), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_0_BCDG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

/-- Split wall `BCDG` / `DD·CCC`, load `delta` (w=5), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_1_BCDG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

/-- Split wall `BCDG` / `DD·CCC`, load `l` (w=1), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_2_BCDG_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

/-- Split wall `CDEG` / `DD·CCC`, load `beta` (w=3), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_3_CDEG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

/-- Split wall `CDEG` / `DD·CCC`, load `delta` (w=5), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_4_CDEG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

/-- Split wall `CDEG` / `DD·CCC`, load `l` (w=1), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_5_CDEG_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

/-- Split wall `CDEG` / `DD·CCC`, load `zeta` (w=7), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_6_CDEG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

/-- Split wall `CDFG` / `DD·CCC`, load `beta` (w=3), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_7_CDFG_Beta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 7 * A.natDegree

/-- Split wall `CDFG` / `DD·CCC`, load `delta` (w=5), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_8_CDFG_Delta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 5 * A.natDegree

/-- Split wall `CDFG` / `DD·CCC`, load `l` (w=1), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_9_CDFG_L810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 9 * A.natDegree

/-- Split wall `CDFG` / `DD·CCC`, load `zeta` (w=7), 13 sub-cells, pattern 6. -/
def quarticWallSplit6_10_CDFG_Zeta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = 3 * A.natDegree

/-- Pattern 7: pivots `n6:CDG, nu:DG` (1 walls, 5 sub-cells). -/
def quarticWallSplitPattern7810Pivots : Prop := True

/-- Split wall `CDEG` / `CG·CCC`, load `theta` (w=9), 5 sub-cells, pattern 7. -/
def quarticWallSplit7_0_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

/-- Pattern 8: pivots `nu:CCD, nu:DG` (3 walls, 5 sub-cells). -/
def quarticWallSplitPattern8810Pivots : Prop := True

/-- Split wall `CDEG` / `CG·DD`, load `theta` (w=9), 5 sub-cells, pattern 8. -/
def quarticWallSplit8_0_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

/-- Split wall `CDEG` / `DD·CCC`, load `theta` (w=9), 5 sub-cells, pattern 8. -/
def quarticWallSplit8_1_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

/-- Split wall `CDFG` / `DD·CCC`, load `theta` (w=9), 5 sub-cells, pattern 8. -/
def quarticWallSplit8_2_CDFG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  4 * D.natDegree = A.natDegree

/-- Pattern 9: pivots `nu:DG` (2 walls, 3 sub-cells). -/
def quarticWallSplitPattern9810Pivots : Prop := True

/-- Split wall `CDEG` / `CG·DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 9. -/
def quarticWallSplit9_0_CDEG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

/-- Split wall `CDFG` / `CG·DD·CCC`, load `theta` (w=9), 3 sub-cells, pattern 9. -/
def quarticWallSplit9_1_CDFG_Theta810
    (A B C D E F G : k[X]) : Prop :=
  2 * C.natDegree + 2 * G.natDegree = 3 * A.natDegree

theorem quarticWallSplit810_ok : True := trivial

end QuarticWallSplit810

/-! ## Axiom audit -/

#print axioms quarticOpenChamberI810_identity
#print axioms quarticOpenChamberI810_impossible
#print axioms quarticOpenChamberII810_identity
#print axioms quarticOpenChamberII810_impossible
#print axioms degreeZeroN4TowerQuartic810_natDegree_le
#print axioms degreeZeroN5TowerQuartic810_natDegree_le
#print axioms degreeZeroN6TowerQuartic810_natDegree_le
#print axioms degreeZeroN7TowerQuartic810_natDegree_le
#print axioms degreeZeroN4Quartic810_star
#print axioms degreeZeroN5Quartic810_star
#print axioms degreeZeroN6Quartic810_star
#print axioms degreeZeroN7Quartic810_star
#print axioms quarticCostChamberBCDEF1810_identity
#print axioms quarticCostChamberBCDEF1810_impossible
#print axioms quarticCostChamberBCDEFG2810_identity
#print axioms quarticCostChamberBCDEFG2810_impossible
#print axioms quarticCostChamberBCDEFG3810_identity
#print axioms quarticCostChamberBCDEFG3810_impossible
#print axioms quarticCostChamberBCDEFG4810_identity
#print axioms quarticCostChamberBCDEFG4810_impossible
#print axioms quarticCostChamberBCDEFG5810_identity
#print axioms quarticCostChamberBCDEFG5810_impossible
#print axioms quarticCostChamberBCDEFG6810_identity
#print axioms quarticCostChamberBCDEFG6810_impossible
#print axioms quarticCostChamberBCDEFG7810_identity
#print axioms quarticCostChamberBCDEFG7810_impossible
#print axioms quarticCostChamberBCDEFG8810_identity
#print axioms quarticCostChamberBCDEFG8810_impossible
#print axioms quarticCostChamberBCDEFG9810_identity
#print axioms quarticCostChamberBCDEFG9810_impossible
#print axioms quarticCostChamberBCDEFG10810_identity
#print axioms quarticCostChamberBCDEFG10810_impossible
#print axioms quarticCostChamberBCDEFG11810_identity
#print axioms quarticCostChamberBCDEFG11810_impossible
#print axioms quarticCostChamberBCDEFG12810_identity
#print axioms quarticCostChamberBCDEFG12810_impossible
#print axioms quarticCostChamberBCDEG13810_identity
#print axioms quarticCostChamberBCDEG13810_impossible
#print axioms quarticCostChamberBCDFG14810_identity
#print axioms quarticCostChamberBCDFG14810_impossible
#print axioms quarticCostChamberBCDFG15810_identity
#print axioms quarticCostChamberBCDFG15810_impossible
#print axioms quarticCostChamberBCEFG16810_identity
#print axioms quarticCostChamberBCEFG16810_impossible
#print axioms quarticCostChamberBCEFG17810_identity
#print axioms quarticCostChamberBCEFG17810_impossible
#print axioms quarticCostChamberBDEFG18810_identity
#print axioms quarticCostChamberBDEFG18810_impossible
#print axioms quarticCostChamberCDEFG19810_identity
#print axioms quarticCostChamberCDEFG19810_impossible
#print axioms quarticSigma_l_eq_zero_of_N7_column
#print axioms quarticSigma_beta_eq_zero_of_N7_column
#print axioms quarticSigma_delta_eq_zero_of_N7_column
#print axioms quarticSigma_zeta_eq_zero_of_N7_column
#print axioms quarticSigma_theta_eq_zero_of_N7_column
#print axioms quarticWallEmpty_BCD6_kappa_Theta810
#print axioms quarticWallEmpty_BCDG16_kappa_Theta810
#print axioms quarticWallEmpty_BCDG17_kappa_Theta810
#print axioms quarticWallEmpty_BCDG18_kappa_Theta810
#print axioms quarticWallEmpty_BCDG24_kappa_Theta810
#print axioms quarticWallEmpty_BDFG7_kappa_Theta810
#print axioms quarticWallEmpty_BDFG7_kappa_Zeta810
#print axioms quarticWallEmpty_BEFG7_kappa_Theta810
#print axioms quarticWallEmpty_BEFG7_kappa_Zeta810
#print axioms quarticWallEmpty_CDFG7_kappa_Theta810
#print axioms quarticWallEmpty_CEFG7_kappa_Theta810
#print axioms quarticWallEmpty_BCDEG30_kappa_Theta810
#print axioms quarticWallEmpty_BCDEG30_nu_Theta810
#print axioms quarticWallEmpty_BCDFG10_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BCDFG10_nu_Theta810
#print axioms quarticWallEmpty_BCDFG10_nu_Zeta810
#print axioms quarticWallEmpty_BCDFG14_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG14_kappa_Zeta810
#print axioms quarticWallEmpty_BCDFG45_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG45_kappa_Zeta810
#print axioms quarticWallEmpty_BCDFG54_kappa_Theta810
#print axioms quarticWallEmpty_BCDFG54_nu_Theta810
#print axioms quarticWallEmpty_BCEFG10_kappa_Theta810
#print axioms quarticWallEmpty_BCEFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BCEFG10_nu_Theta810
#print axioms quarticWallEmpty_BCEFG10_nu_Zeta810
#print axioms quarticWallEmpty_BCEFG14_kappa_Theta810
#print axioms quarticWallEmpty_BCEFG14_kappa_Zeta810
#print axioms quarticWallEmpty_BCEFG45_kappa_Theta810
#print axioms quarticWallEmpty_BCEFG45_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG7_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG7_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG7_nu_Theta810
#print axioms quarticWallEmpty_BDEFG7_nu_Zeta810
#print axioms quarticWallEmpty_BDEFG10_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG13_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG13_kappa_Zeta810
#print axioms quarticWallEmpty_BDEFG39_kappa_Theta810
#print axioms quarticWallEmpty_BDEFG39_kappa_Zeta810
#print axioms quarticWallEmpty_CDEFG7_kappa_Theta810
#print axioms quarticWallEmpty_CDEFG7_nu_Theta810
#print axioms quarticWallEmpty_CDEFG10_kappa_Theta810
#print axioms quarticWallEmpty_CDEFG13_kappa_Theta810
#print axioms quarticWallEmpty_CDEFG39_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG10_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG10_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG10_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG10_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG10_omicron_Theta810
#print axioms quarticWallEmpty_BCDEFG10_omicron_Zeta810
#print axioms quarticWallEmpty_BCDEFG13_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG13_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG13_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG13_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG16_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG16_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG16_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG16_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG20_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG20_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG20_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG20_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG23_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG23_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG26_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG26_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG81_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG81_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG81_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG81_nu_Zeta810
#print axioms quarticWallEmpty_BCDEFG84_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG84_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG87_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG87_kappa_Zeta810
#print axioms quarticWallEmpty_BCDEFG102_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG102_nu_Theta810
#print axioms quarticWallEmpty_BCDEFG115_kappa_Theta810
#print axioms quarticWallEmpty_BCDEFG115_kappa_Zeta810
#print axioms quarticCost_CCD_wall_trichotomy
#print axioms quarticCost_DDD_wall_trichotomy
#print axioms quarticCost_CDG_wall_trichotomy
#print axioms quarticCost_DG_wall_trichotomy
#print axioms quarticCost_CCCD_wall_trichotomy

end Max11DegreeRoutes
