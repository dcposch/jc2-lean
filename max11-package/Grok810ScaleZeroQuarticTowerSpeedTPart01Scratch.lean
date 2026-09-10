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

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₄`. -/
def n4QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (495 / 268435456 * l : k) • A ^ 8

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₄`. -/
def n4QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (15 / 2097152 * beta : k) • A ^ 7

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₄`. -/
def n4QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (7 / 262144 * delta : k) • A ^ 6

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₄`. -/
def n4QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (3 / 32768 * zeta : k) • A ^ 5

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₅`. -/
def n5QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (429 / 33554432 * l : k) • A ^ 7

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₅`. -/
def n5QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₅`. -/
def n5QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (63 / 262144 * delta : k) • A ^ 5

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₅`. -/
def n5QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₆`. -/
def n6QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (715 / 268435456 * l : k) • A ^ 8

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₆`. -/
def n6QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (11 / 1048576 * beta : k) • A ^ 7

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₆`. -/
def n6QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (21 / 524288 * delta : k) • A ^ 6

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₆`. -/
def n6QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (7 / 49152 * zeta : k) • A ^ 5

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₇`. -/
def n7QuarticLTowerFace810 (l : k) (A : k[X]) : k[X] :=
  (6435 / 268435456 * l : k) • A ^ 8

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₇`. -/
def n7QuarticBetaTowerFace810 (beta : k) (A : k[X]) : k[X] :=
  (429 / 4194304 * beta : k) • A ^ 7

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₇`. -/
def n7QuarticDeltaTowerFace810 (delta : k) (A : k[X]) : k[X] :=
  (231 / 524288 * delta : k) • A ^ 6

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₇`. -/
def n7QuarticZetaTowerFace810 (zeta : k) (A : k[X]) : k[X] :=
  (63 / 32768 * zeta : k) • A ^ 5

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
def kappaQuarticOpenIFace810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f

set_option maxHeartbeats 64000000 in
def muQuarticOpenIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * c ^ 3 + 32 * c * g

set_option maxHeartbeats 64000000 in
def piQuarticOpenIFace810 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f
  + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def n5QuarticOpenIFace810 (a b c d e f g : k) : k :=
  7 * a * b ^ 3 * c + (-8 : k) * a * b ^ 2 * f + (-36 : k) * b * c ^ 3 + 96 * b * c * g + 64 * c ^ 2 * f
  + (-256 : k) * f * g

set_option maxHeartbeats 64000000 in
def kappaQuarticOpenICofactor810 (a b c d e f g : k) : k :=
  17 * a * b ^ 2 * c * g + (-10 : k) * a * b * c ^ 2 * f + (-16 : k) * a * b * f * g + 16 * a * c * f ^ 2
  + (-20 : k) * c ^ 3 * g + 512 * c * g ^ 2

set_option maxHeartbeats 64000000 in
def muQuarticOpenICofactor810 (a b c d e f g : k) : k :=
  3 * a * b ^ 3 * g + (-6 : k) * a * b ^ 2 * c * f + 8 * a * b * f ^ 2 + (-60 : k) * b * c ^ 2 * g
  + 288 * b * g ^ 2 + 64 * c * f * g

set_option maxHeartbeats 64000000 in
def piQuarticOpenICofactor810 (a b c d e f g : k) : k :=
  (-4 : k) * b * c * g + 8 * f * g

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
def kappaQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  a * b ^ 3 + (-12 : k) * b * c ^ 2 + 32 * b * g + 32 * c * f + 32 * d * e

set_option maxHeartbeats 64000000 in
def muQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * c + (-8 : k) * a * b * f + (-4 : k) * a * d ^ 2 + (-4 : k) * c ^ 3 + 32 * c * g
  + 16 * e ^ 2

set_option maxHeartbeats 64000000 in
def xiQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * e + 6 * a * b * c * d + (-8 : k) * a * d * f + (-12 : k) * c ^ 2 * e + 32 * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_piQuarticOpenIIFace810_chunk01 (a b c d e f g : k) : k :=
  3 * a ^ 2 * b ^ 4 + (-72 : k) * a * b ^ 2 * c ^ 2 + 64 * a * b ^ 2 * g + 128 * a * b * c * f + 256 * a * b * d * e + 128 * a * c * d ^ 2 + (-256 : k) * a * f ^ 2 + 48 * c ^ 4 + (-256 : k) * c ^ 2 * g + (-512 : k) * c * e ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_piQuarticOpenIIFace810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + 1024 * g ^ 2

set_option maxHeartbeats 64000000 in
def piQuarticOpenIIFace810 (a b c d e f g : k) : k :=
  towerSpeedT_piQuarticOpenIIFace810_chunk02 a b c d e f g (towerSpeedT_piQuarticOpenIIFace810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n2QuarticOpenIIFace810 (a b c d e f g : k) : k :=
  3 * a * b ^ 2 * d + (-24 : k) * b * c * e + (-12 : k) * c ^ 2 * d + 32 * d * g + 32 * e * f

set_option maxHeartbeats 64000000 in
def n6QuarticOpenIIFace810 (a b c d e f g : k) : k :=
  29 * a * b ^ 3 * c + (-40 : k) * a * b ^ 2 * f + (-80 : k) * a * b * d ^ 2 + (-108 : k) * b * c ^ 3
  + 288 * b * c * g + 320 * b * e ^ 2 + 128 * c ^ 2 * f + 608 * c * d * e + (-1280 : k) * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticOpenIICofactor810_chunk01 (a b c d e f g : k) : k :=
  (-25080 : k) * a ^ 2 * b ^ 3 * d * f + 291480 * a ^ 2 * b ^ 2 * d ^ 3 + (-433136 : k) * a * b ^ 2 * c * d * g + (-8095920 : k) * a * b ^ 2 * d * e ^ 2 + (-1167232 : k) * a * b * c ^ 2 * d * f + (-14803488 : k) * a * b * c * d ^ 2 * e + (-6960640 : k) * a * b * d * f * g + 694176 * a * c ^ 2 * d ^ 3 + 650496 * a * c * d * f ^ 2 + 4620000 * a * d ^ 3 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_kappaQuarticOpenIICofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + 27720000 * a * d ^ 2 * e * f + 2535104 * c ^ 3 * d * g + 24943296 * c ^ 2 * d * e ^ 2 + (-2601984 : k) * c * d * g ^ 2 + 83699712 * c * e * f * g + (-92400000 : k) * d * e ^ 2 * g

set_option maxHeartbeats 64000000 in
def kappaQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_kappaQuarticOpenIICofactor810_chunk02 a b c d e f g (towerSpeedT_kappaQuarticOpenIICofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticOpenIICofactor810_chunk01 (a b c d e f g : k) : k :=
  (-731280 : k) * a * b ^ 3 * d * g + (-1362240 : k) * a * b ^ 2 * c * d * f + (-5103840 : k) * a * b ^ 2 * d ^ 2 * e + (-1985340 : k) * a * b * c * d ^ 3 + 880000 * a * b * d * f ^ 2 + 6930000 * a * d ^ 3 * f + 2122560 * b * c ^ 2 * d * g + 49521360 * b * c * d * e ^ 2 + (-3520000 : k) * b * d * g ^ 2 + 88104960 * b * e * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_muQuarticOpenIICofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-401280 : k) * c ^ 3 * d * f + 37047360 * c ^ 2 * d ^ 2 * e + 27842560 * c * d * f * g + (-110880000 : k) * d ^ 2 * e * g + (-83160000 : k) * d * e ^ 2 * f

set_option maxHeartbeats 64000000 in
def muQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_muQuarticOpenIICofactor810_chunk02 a b c d e f g (towerSpeedT_muQuarticOpenIICofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_xiQuarticOpenIICofactor810_chunk01 (a b c d e f g : k) : k :=
  2552900 * a * b ^ 3 * d * e + 1306200 * a * b ^ 2 * c * d ^ 2 + (-3909040 : k) * a * b * d ^ 2 * f + (-3465000 : k) * a * d ^ 4 + (-28324800 : k) * b * c ^ 2 * d * e + (-36710400 : k) * b * c * f * g + 80316160 * b * d * e * g + (-971600 : k) * c ^ 3 * d ^ 2 + 12556160 * c * d ^ 2 * g + 77236160 * c * d * e * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_xiQuarticOpenIICofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + 106260000 * d ^ 2 * e ^ 2 + 127262720 * f ^ 2 * g

set_option maxHeartbeats 64000000 in
def xiQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_xiQuarticOpenIICofactor810_chunk02 a b c d e f g (towerSpeedT_xiQuarticOpenIICofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def piQuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  8360 * a * b ^ 2 * d * f + (-36435 : k) * a * b * d ^ 3 + (-66880 : k) * b * c * d * g
  + 145740 * b * d * e ^ 2 + (-33440 : k) * c ^ 2 * d * f + 291480 * c * d ^ 2 * e
  + (-2829440 : k) * d * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticOpenIICofactor810_chunk01 (a b c d e f g : k) : k :=
  (-60725 : k) * a ^ 2 * b ^ 3 * d ^ 2 + 7081200 * a * b ^ 2 * c * d * e + 4588800 * a * b ^ 2 * f * g + 1306200 * a * b * c ^ 2 * d ^ 2 + (-1599040 : k) * a * b * d ^ 2 * g + (-17769040 : k) * a * b * d * e * f + (-2369040 : k) * a * c * d ^ 2 * f + (-15015000 : k) * a * d ^ 3 * e + (-10211600 : k) * c ^ 3 * d * e + (-18355200 : k) * c ^ 2 * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_n2QuarticOpenIICofactor810_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + 74156160 * c * d * e * g + 41580000 * d * e ^ 3 + 127262720 * f * g ^ 2

set_option maxHeartbeats 64000000 in
def n2QuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  towerSpeedT_n2QuarticOpenIICofactor810_chunk02 a b c d e f g (towerSpeedT_n2QuarticOpenIICofactor810_chunk01 a b c d e f g)

set_option maxHeartbeats 64000000 in
def n6QuarticOpenIICofactor810 (a b c d e f g : k) : k :=
  97504 * a * b ^ 2 * d * g + 195008 * a * b * c * d * f + (-437808 : k) * a * b * d ^ 2 * e
  + (-218904 : k) * a * c * d ^ 3 + (-229504 : k) * a * d * f ^ 2 + (-390016 : k) * c ^ 2 * d * g
  + 875616 * c * d * e ^ 2 + 918016 * d * g ^ 2 + (-4405248 : k) * e * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk01 (a b c d e f g : k) : k :=
  (-25080 : k) * a ^ 3 * b ^ 6 * d * f + 291480 * a ^ 3 * b ^ 5 * d ^ 3 + (-2626976 : k) * a ^ 2 * b ^ 5 * c * d * g + (-8095920 : k) * a ^ 2 * b ^ 5 * d * e ^ 2 + (-4952992 : k) * a ^ 2 * b ^ 4 * c ^ 2 * d * f + (-30115008 : k) * a ^ 2 * b ^ 4 * c * d ^ 2 * e + (-1912960 : k) * a ^ 2 * b ^ 4 * d * f * g + (-8759604 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + 13385856 * a ^ 2 * b ^ 3 * c * d * f ^ 2 + 16872480 * a ^ 2 * b ^ 3 * d ^ 3 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + 67748160 * a ^ 2 * b ^ 3 * d ^ 2 * e * f + 51449040 * a ^ 2 * b ^ 2 * c * d ^ 3 * f + 29742720 * a ^ 2 * b ^ 2 * d ^ 4 * e + (-7040000 : k) * a ^ 2 * b ^ 2 * d * f ^ 3 + 7941360 * a ^ 2 * b * c * d ^ 5 + (-58960000 : k) * a ^ 2 * b * d ^ 3 * f ^ 2 + (-27720000 : k) * a ^ 2 * d ^ 5 * f + 17025536 * a * b ^ 3 * c ^ 3 * d * g + 270658416 * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (-50423296 : k) * a * b ^ 3 * c * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + 348014592 * a * b ^ 3 * c * e * f * g + (-363169920 : k) * a * b ^ 3 * d * e ^ 2 * g + 18251904 * a * b ^ 2 * c ^ 4 * d * f + 309199296 * a * b ^ 2 * c ^ 3 * d ^ 2 * e + 55271424 * a * b ^ 2 * c ^ 2 * d * f * g + (-983534848 : k) * a * b ^ 2 * c * d ^ 2 * e * g + (-926516160 : k) * a * b ^ 2 * c * d * e ^ 2 * f + (-340730880 : k) * a * b ^ 2 * d ^ 2 * e ^ 3 + (-194580480 : k) * a * b ^ 2 * d * f * g ^ 2 + (-704839680 : k) * a * b ^ 2 * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-388752 : k) * a * b * c ^ 4 * d ^ 3 + (-45467136 : k) * a * b * c ^ 3 * d * f ^ 2 + (-105247488 : k) * a * b * c ^ 2 * d ^ 3 * g + (-1140081920 : k) * a * b * c ^ 2 * d ^ 2 * e * f + (-703562496 : k) * a * b * c * d ^ 3 * e ^ 2 + (-396505088 : k) * a * b * c * d * f ^ 2 * g + 161920000 * a * b * d ^ 3 * g ^ 2 + 1198919680 * a * b * d ^ 2 * e * f * g + 679360000 * a * b * d * e ^ 2 * f ^ 2 + (-3901248 : k) * a * c ^ 3 * d ^ 3 * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-125975808 : k) * a * c ^ 2 * d ^ 4 * e + 20815872 * a * c ^ 2 * d * f ^ 3 + 258229760 * a * c * d ^ 3 * f * g + 907855872 * a * c * d ^ 2 * e * f ^ 2 + 591360000 * a * d ^ 4 * e * g + 1330560000 * a * d ^ 3 * e ^ 2 * f + (-38911488 : k) * b * c ^ 5 * d * g + (-497404992 : k) * b * c ^ 4 * d * e ^ 2 + 194349056 * b * c ^ 3 * d * g ^ 2 + (-1356816384 : k) * b * c ^ 3 * e * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk06 (a b c d e f g : k) (acc : k) : k :=
  acc + 3525629952 * b * c ^ 2 * d * e ^ 2 * g + 792341760 * b * c * d * e ^ 4 + (-195903488 : k) * b * c * d * g ^ 3 + 5497749504 * b * c * e * f * g ^ 2 + (-3013120000 : k) * b * d * e ^ 2 * g ^ 2 + 1409679360 * b * e ^ 3 * f * g + 1605120 * c ^ 6 * d * f + (-148189440 : k) * c ^ 5 * d ^ 2 * e + (-43087872 : k) * c ^ 4 * d * f * g + 1710158848 * c ^ 3 * d ^ 2 * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk07 (a b c d e f g : k) (acc : k) : k :=
  acc + 1124404992 * c ^ 3 * d * e ^ 2 * f + 1390943232 * c ^ 2 * d ^ 2 * e ^ 3 + 807698432 * c ^ 2 * d * f * g ^ 2 + 2678390784 * c ^ 2 * e * f ^ 2 * g + (-3631423488 : k) * c * d ^ 2 * e * g ^ 2 + (-2494048256 : k) * c * d * e ^ 2 * f * g + (-4730880000 : k) * d ^ 2 * e ^ 3 * g + (-1330560000 : k) * d * e ^ 4 * f

set_option maxHeartbeats 64000000 in
def quarticOpenChamberII810_identityPartial1 (a b c d e f g : k) : k :=
  towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk07 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk06 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk05 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk04 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk03 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk02 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial1_chunk01 a b c d e f g))))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk01 (a b c d e f g : k) : k :=
  25080 * a ^ 3 * b ^ 6 * d * f + (-109305 : k) * a ^ 3 * b ^ 5 * d ^ 3 + (-200640 : k) * a ^ 2 * b ^ 5 * c * d * g + 8095920 * a ^ 2 * b ^ 5 * d * e ^ 2 + (-702240 : k) * a ^ 2 * b ^ 4 * c ^ 2 * d * f + 20110440 * a ^ 2 * b ^ 4 * c * d ^ 2 * e + (-7953280 : k) * a ^ 2 * b ^ 4 * d * f * g + 10460520 * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + 1070080 * a ^ 2 * b ^ 3 * c * d * f ^ 2 + (-2331840 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-30010160 : k) * a ^ 2 * b ^ 3 * d ^ 2 * e * f + (-37497440 : k) * a ^ 2 * b ^ 2 * c * d ^ 3 * f + (-19722360 : k) * a ^ 2 * b ^ 2 * d ^ 4 * e + (-2140160 : k) * a ^ 2 * b ^ 2 * d * f ^ 3 + (-25453680 : k) * a ^ 2 * b * c * d ^ 5 + 40599680 * a ^ 2 * b * d ^ 3 * f ^ 2 + 27720000 * a ^ 2 * d ^ 5 * f + 4815360 * a * b ^ 3 * c ^ 3 * d * g + (-126102480 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + (-4280320 : k) * a * b ^ 3 * c * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-110131200 : k) * a * b ^ 3 * c * e * f * g + 331968640 * a * b ^ 3 * d * e ^ 2 * g + 2808960 * a * b ^ 2 * c ^ 4 * d * f + (-209524560 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-29383680 : k) * a * b ^ 2 * c ^ 2 * d * f * g + 562897280 * a * b ^ 2 * c * d ^ 2 * e * g + 246082880 * a * b ^ 2 * c * d * e ^ 2 * f + 356089440 * a * b ^ 2 * d ^ 2 * e ^ 3 + (-172523520 : k) * a * b ^ 2 * d * f * g ^ 2 + 381788160 * a * b ^ 2 * e * f ^ 2 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + (-7578480 : k) * a * b * c ^ 4 * d ^ 3 + (-4280320 : k) * a * b * c ^ 3 * d * f ^ 2 + 76103680 * a * b * c ^ 2 * d ^ 3 * g + 765672640 * a * b * c ^ 2 * d ^ 2 * e * f + 749488320 * a * b * c * d ^ 3 * e ^ 2 + 712212480 * a * b * c * d * f ^ 2 * g + (-37309440 : k) * a * b * d ^ 3 * g ^ 2 + (-1491955200 : k) * a * b * d ^ 2 * e * f * g + (-37309440 : k) * a * b * d * e ^ 2 * f ^ 2 + 3492480 * a * c ^ 3 * d ^ 3 * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + 78889440 * a * c ^ 2 * d ^ 4 * e + 8560640 * a * c ^ 2 * d * f ^ 3 + (-462617600 : k) * a * c * d ^ 3 * f * g + (-692508160 : k) * a * c * d ^ 2 * e * f ^ 2 + (-110880000 : k) * a * d ^ 4 * e * g + (-850080000 : k) * a * d ^ 3 * e ^ 2 * f + (-293765120 : k) * a * d * f ^ 3 * g + (-3210240 : k) * b * c ^ 5 * d * g + 346893120 * b * c ^ 4 * d * e ^ 2 + 17121280 * b * c ^ 3 * d * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk06 (a b c d e f g : k) (acc : k) : k :=
  acc + 440524800 * b * c ^ 3 * e * f * g + (-1873254400 : k) * b * c ^ 2 * d * e ^ 2 * g + (-74618880 : k) * b * c * d * e ^ 4 + (-68485120 : k) * b * c * d * g ^ 3 + (-1174732800 : k) * b * c * e * f * g ^ 2 + 2719354880 * b * d * e ^ 2 * g ^ 2 + (-1605120 : k) * c ^ 6 * d * f + 25650240 * c ^ 5 * d ^ 2 * e + (-127252480 : k) * c ^ 4 * d * f * g + (-256384000 : k) * c ^ 3 * d ^ 2 * e * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk07 (a b c d e f g : k) (acc : k) : k :=
  acc + (-909712640 : k) * c ^ 3 * d * e ^ 2 * f + (-1424357760 : k) * c ^ 2 * d ^ 2 * e ^ 3 + 690094080 * c ^ 2 * d * f * g ^ 2 + (-1527152640 : k) * c ^ 2 * e * f ^ 2 * g + 700272640 * c * d ^ 2 * e * g ^ 2 + 3920230400 * c * d * e ^ 2 * f * g + 3400320000 * d ^ 2 * e ^ 3 * g + (-2897346560 : k) * d * f * g ^ 3 + 4072407040 * e * f ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticOpenChamberII810_identityPartial2 (a b c d e f g : k) : k :=
  towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk07 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk06 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk05 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk04 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk03 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk02 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial2_chunk01 a b c d e f g))))))

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk01 (a b c d e f g : k) : k :=
  (-182175 : k) * a ^ 3 * b ^ 5 * d ^ 3 + 2827616 * a ^ 2 * b ^ 5 * c * d * g + 5655232 * a ^ 2 * b ^ 4 * c ^ 2 * d * f + 10004568 * a ^ 2 * b ^ 4 * c * d ^ 2 * e + 9866240 * a ^ 2 * b ^ 4 * d * f * g + (-1700916 : k) * a ^ 2 * b ^ 3 * c ^ 2 * d ^ 3 + (-14455936 : k) * a ^ 2 * b ^ 3 * c * d * f ^ 2 + (-14540640 : k) * a ^ 2 * b ^ 3 * d ^ 3 * g + (-37738000 : k) * a ^ 2 * b ^ 3 * d ^ 2 * e * f + (-13951600 : k) * a ^ 2 * b ^ 2 * c * d ^ 3 * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk02 (a b c d e f g : k) (acc : k) : k :=
  acc + (-10020360 : k) * a ^ 2 * b ^ 2 * d ^ 4 * e + 9180160 * a ^ 2 * b ^ 2 * d * f ^ 3 + 17512320 * a ^ 2 * b * c * d ^ 5 + 18360320 * a ^ 2 * b * d ^ 3 * f ^ 2 + (-21840896 : k) * a * b ^ 3 * c ^ 3 * d * g + (-144555936 : k) * a * b ^ 3 * c ^ 2 * d * e ^ 2 + 54703616 * a * b ^ 3 * c * d * g ^ 2 + (-237883392 : k) * a * b ^ 3 * c * e * f * g + 31201280 * a * b ^ 3 * d * e ^ 2 * g + (-21060864 : k) * a * b ^ 2 * c ^ 4 * d * f

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk03 (a b c d e f g : k) (acc : k) : k :=
  acc + (-99674736 : k) * a * b ^ 2 * c ^ 3 * d ^ 2 * e + (-25887744 : k) * a * b ^ 2 * c ^ 2 * d * f * g + 420637568 * a * b ^ 2 * c * d ^ 2 * e * g + 680433280 * a * b ^ 2 * c * d * e ^ 2 * f + (-15358560 : k) * a * b ^ 2 * d ^ 2 * e ^ 3 + 367104000 * a * b ^ 2 * d * f * g ^ 2 + 323051520 * a * b ^ 2 * e * f ^ 2 * g + 7967232 * a * b * c ^ 4 * d ^ 3 + 49747456 * a * b * c ^ 3 * d * f ^ 2 + 29143808 * a * b * c ^ 2 * d ^ 3 * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk04 (a b c d e f g : k) (acc : k) : k :=
  acc + 374409280 * a * b * c ^ 2 * d ^ 2 * e * f + (-45925824 : k) * a * b * c * d ^ 3 * e ^ 2 + (-315707392 : k) * a * b * c * d * f ^ 2 * g + (-124610560 : k) * a * b * d ^ 3 * g ^ 2 + 293035520 * a * b * d ^ 2 * e * f * g + (-642050560 : k) * a * b * d * e ^ 2 * f ^ 2 + 408768 * a * c ^ 3 * d ^ 3 * f + 47086368 * a * c ^ 2 * d ^ 4 * e + (-29376512 : k) * a * c ^ 2 * d * f ^ 3 + 204387840 * a * c * d ^ 3 * f * g

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk05 (a b c d e f g : k) (acc : k) : k :=
  acc + (-215347712 : k) * a * c * d ^ 2 * e * f ^ 2 + (-480480000 : k) * a * d ^ 4 * e * g + (-480480000 : k) * a * d ^ 3 * e ^ 2 * f + 293765120 * a * d * f ^ 3 * g + 42121728 * b * c ^ 5 * d * g + 150511872 * b * c ^ 4 * d * e ^ 2 + (-211470336 : k) * b * c ^ 3 * d * g ^ 2 + 916291584 * b * c ^ 3 * e * f * g + (-1652375552 : k) * b * c ^ 2 * d * e ^ 2 * g + (-717722880 : k) * b * c * d * e ^ 4

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk06 (a b c d e f g : k) (acc : k) : k :=
  acc + 264388608 * b * c * d * g ^ 3 + (-4323016704 : k) * b * c * e * f * g ^ 2 + 293765120 * b * d * e ^ 2 * g ^ 2 + (-1409679360 : k) * b * e ^ 3 * f * g + 122539200 * c ^ 5 * d ^ 2 * e + 170340352 * c ^ 4 * d * f * g + (-1453774848 : k) * c ^ 3 * d ^ 2 * e * g + (-214692352 : k) * c ^ 3 * d * e ^ 2 * f + 33414528 * c ^ 2 * d ^ 2 * e ^ 3 + (-1497792512 : k) * c ^ 2 * d * f * g ^ 2

set_option maxHeartbeats 64000000 in
private abbrev towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk07 (a b c d e f g : k) (acc : k) : k :=
  acc + (-1151238144 : k) * c ^ 2 * e * f ^ 2 * g + 2931150848 * c * d ^ 2 * e * g ^ 2 + (-1426182144 : k) * c * d * e ^ 2 * f * g + 1330560000 * d ^ 2 * e ^ 3 * g + 1330560000 * d * e ^ 4 * f + 2897346560 * d * f * g ^ 3 + 9711124480 * e * f ^ 2 * g ^ 2

set_option maxHeartbeats 64000000 in
def quarticOpenChamberII810_identityPartial3 (a b c d e f g : k) : k :=
  towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk07 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk06 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk05 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk04 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk03 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk02 a b c d e f g (towerSpeedT_quarticOpenChamberII810_identityPartial3_chunk01 a b c d e f g))))))

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

end Max11DegreeRoutes
