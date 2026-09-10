import Grok810ScaleZeroQuarticChamberN7LadderScratch
import Grok810ScaleZeroQuarticChamberInfraN5Scratch
import Grok810ScaleZeroQuarticLoadLadderScratch
import Max11SpeedReflectDegLibScratch

/-! # The cost-form `N₅` load ladder, `(8,10)` scale zero

`UNOWNED_CHAMBERS.md` needs an `n5-cost` band on 370 system rows and 49 single columns.  Same shape as the `κ`/`N₂` ladder: one cost inequality per minimal load-free monomial of `N₅`, plus one per minimal monomial of each lighter `γ/ε/η` column.  Independent of the `N₇` ladder.  Untracked working note.
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

section QuarticCostLadderN5810

/-! ## `N₅` in cost form: `c₀(N₅) > w_π·a` instead of `2·s_X > w_π·a` -/

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 1/5): 20 monomials. -/
def n5QuarticCostRestL810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  - (225 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (315 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 65536 * l : k) • (A ^ 3 * B * D)
  + (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  + (9 / 65536 * l : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 2/5): 20 monomials. -/
def n5QuarticCostRestL810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(441 / 262144 * l : k)) • (A * B ^ 4)
  + (45 / 8192 * l : k) • (A ^ 3 * G)
  - (27 / 8192 * l : k) • (A ^ 2 * B * F)
  + (27 / 4096 * l : k) • (A ^ 2 * C * E)
  - (9 / 16384 * l : k) • (A ^ 2 * D ^ 2)
  + (27 / 8192 * l : k) • (A * B ^ 2 * E)
  + (9 / 1024 * l : k) • (A * B * C * D)
  - (3 / 2048 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 256 * l : k) • (A * C * G)
  - (9 / 512 * l : k) • (A * D * F)
  + (9 / 1024 * l : k) • (A * E ^ 2)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)
  + (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 3/5): 20 monomials. -/
def n5QuarticCostRestL810c3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)
  - (7 / 2048 * beta : k) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 4/5): 20 monomials. -/
def n5QuarticCostRestL810c4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (D * E)
  + (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 5/5): 8 monomials. -/
def n5QuarticCostRestL810c5
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 128 * zeta : k)) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
def n5QuarticCostRestL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestL810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestL810c4 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestL810c5 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₅` splits
into its pure-`A` `l` column `c·l·A^7` and the rest. -/
theorem degreeZeroN5Quartic810_eq_lCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticLFace810 l A +
        n5QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN5Quartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n5QuarticLFace810, n5QuarticCostRestL810, n5QuarticCostRestL810c1, n5QuarticCostRestL810c2, n5QuarticCostRestL810c3, n5QuarticCostRestL810c4, n5QuarticCostRestL810c5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestL810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c1s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 4096) : k), (-(21 / 4096) : k), (5 / 512 : k),
      (5 / 256 : k), (5 / 128 : k), (135 / 1024 : k)
      ]
      [
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 0, 2, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c1s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c1s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestL810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c1s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (-(15 / 128) : k), (-(5 / 32) : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c1s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c1s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestL810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3
  + (5 / 16 : k) • (F * G)
  + (315 / 1048576 * l : k) • (A ^ 5 * C)
  - (225 / 4194304 * l : k) • (A ^ 4 * B ^ 2)
  + (315 / 262144 * l : k) • (A ^ 4 * E)
  - (27 / 65536 * l : k) • (A ^ 3 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c1s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (5 / 16 : k), (315 / 1048576 * l : k),
      (-(225 / 4194304 * l) : k), (315 / 262144 * l : k), (-(27 / 65536 * l) : k)
      ]
      [
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c1s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c1s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestL810c1`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (135 / 131072 * l : k) • (A ^ 3 * C ^ 2)
  + (9 / 65536 * l : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c1s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (135 / 131072 * l : k), (9 / 65536 * l : k)
      ]
      [
      [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c1s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c1s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c1s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c1_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestL810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestL810c1, n5QuarticCostRestL810c1s1, n5QuarticCostRestL810c1s2, n5QuarticCostRestL810c1s3, n5QuarticCostRestL810c1s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [n5QuarticCostRestL810c1_split l beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestL810c1s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestL810c1s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c1s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c1s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestL810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(441 / 262144 * l : k)) • (A * B ^ 4)
  + (45 / 8192 * l : k) • (A ^ 3 * G)
  - (27 / 8192 * l : k) • (A ^ 2 * B * F)
  + (27 / 4096 * l : k) • (A ^ 2 * C * E)
  - (9 / 16384 * l : k) • (A ^ 2 * D ^ 2)
  + (27 / 8192 * l : k) • (A * B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c2s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(441 / 262144 * l) : k), (45 / 8192 * l : k), (-(27 / 8192 * l) : k),
      (27 / 4096 * l : k), (-(9 / 16384 * l) : k), (27 / 8192 * l : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c2s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c2s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestL810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 1024 * l : k) • (A * B * C * D)
  - (3 / 2048 * l : k) • (A * C ^ 3)
  + (189 / 8192 * l : k) • (B ^ 3 * D)
  + (567 / 16384 * l : k) • (B ^ 2 * C ^ 2)
  + (9 / 256 * l : k) • (A * C * G)
  - (9 / 512 * l : k) • (A * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c2s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 1024 * l : k), (-(3 / 2048 * l) : k), (189 / 8192 * l : k),
      (567 / 16384 * l : k), (9 / 256 * l : k), (-(9 / 512 * l) : k)
      ]
      [
      [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [n5QuarticCostRestL810c2s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c2s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestL810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 1024 * l : k) • (A * E ^ 2)
  - (27 / 1024 * l : k) • (B ^ 2 * G)
  - (9 / 128 * l : k) • (B * C * F)
  - (45 / 512 * l : k) • (B * D * E)
  - (45 / 1024 * l : k) • (C ^ 2 * E)
  - (27 / 512 * l : k) • (C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c2s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 1024 * l : k), (-(27 / 1024 * l) : k), (-(9 / 128 * l) : k),
      (-(45 / 512 * l) : k), (-(45 / 1024 * l) : k), (-(27 / 512 * l) : k)
      ]
      [
      [1, 0, 0, 0, 2, 0, 0], [0, 2, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c2s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c2s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestL810c2`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c2s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * l : k) • (E * G)
  + (9 / 128 * l : k) • F ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c2s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * l : k), (9 / 128 * l : k)
      ]
      [
      [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 2, 0]
      ] := by
  simp only [n5QuarticCostRestL810c2s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c2s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c2s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestL810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestL810c2, n5QuarticCostRestL810c2s1, n5QuarticCostRestL810c2s2, n5QuarticCostRestL810c2s3, n5QuarticCostRestL810c2s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [n5QuarticCostRestL810c2_split l beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestL810c2s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestL810c2s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c2s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c2s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestL810c3`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c3s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (231 / 4194304 * beta : k) • A ^ 6
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c3s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c3s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (231 / 4194304 * beta : k), (35 / 32768 * beta : k), (-(21 / 131072 * beta) : k),
      (35 / 8192 * beta : k), (-(7 / 8192 * beta) : k), (21 / 16384 * beta : k)
      ]
      [
      [6, 0, 0, 0, 0, 0, 0], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0],
      [2, 1, 0, 1, 0, 0, 0], [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c3s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c3s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c3s1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestL810c3`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c3s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 2048 * beta : k)) • (A * B ^ 2 * C)
  - (189 / 32768 * beta : k) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c3s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c3s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 2048 * beta) : k), (-(189 / 32768 * beta) : k), (21 / 1024 * beta : k),
      (-(7 / 512 * beta) : k), (7 / 1024 * beta : k), (35 / 1024 * beta : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c3s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c3s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c3s2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestL810c3`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c3s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c3s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c3s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 256 * beta : k), (7 / 512 * beta : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (-(1 / 256 * gamma) : k), (9 / 128 * gamma : k)
      ]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c3s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c3s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c3s3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestL810c3`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c3s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c3s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c3s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k)
      ]
      [
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticCostRestL810c3s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c3s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c3s4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c3s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c3_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestL810c3s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c3s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c3s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c3s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestL810c3, n5QuarticCostRestL810c3s1, n5QuarticCostRestL810c3s2, n5QuarticCostRestL810c3s3, n5QuarticCostRestL810c3s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [n5QuarticCostRestL810c3_split l beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestL810c3s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestL810c3s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c3s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c3s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestL810c4`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c4s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (D * E)
  + (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c4s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c4s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k), (63 / 262144 * delta : k), (15 / 4096 * delta : k),
      (-(5 / 16384 * delta) : k), (15 / 1024 * delta : k), (5 / 512 * delta : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c4s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c4s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c4s1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestL810c4`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c4s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 1024 * delta : k)) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c4s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c4s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 1024 * delta) : k), (45 / 512 * delta : k), (5 / 64 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k)
      ]
      [
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c4s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c4s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c4s2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestL810c4`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c4s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c4s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c4s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 32 * epsilon : k), (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k),
      (35 / 32768 * zeta : k), (3 / 256 * zeta : k), (3 / 1024 * zeta : k)
      ]
      [
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c4s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c4s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c4s3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestL810c4`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c4s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c4s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c4s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * zeta : k), (-(9 / 64 * zeta) : k)
      ]
      [
      [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c4s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c4s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c4s4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c4s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c4_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestL810c4s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c4s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c4s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c4s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestL810c4, n5QuarticCostRestL810c4s1, n5QuarticCostRestL810c4s2, n5QuarticCostRestL810c4s3, n5QuarticCostRestL810c4s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [n5QuarticCostRestL810c4_split l beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestL810c4s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestL810c4s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c4s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c4s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/2 of `n5QuarticCostRestL810c5`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c5s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 128 * zeta : k)) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c5s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c5s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c5s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(3 / 32 * eta) : k),
      (1 / 4 * eta : k), (5 / 1024 * theta : k), (1 / 32 * theta : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c5s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c5s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c5s1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c5s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/2 of `n5QuarticCostRestL810c5`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestL810c5s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 128 * theta : k)) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestL810c5s2` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c5s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c5s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 128 * theta) : k), (1 / 8 * theta : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestL810c5s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c5s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c5s2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestL810c5s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c5_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestL810c5 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestL810c5s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestL810c5s2 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestL810c5, n5QuarticCostRestL810c5s1, n5QuarticCostRestL810c5s2]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810c5_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810c5 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  rw [n5QuarticCostRestL810c5_split l beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (n5QuarticCostRestL810c5s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestL810c5s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestL810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp8 : 3 * D.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp13 : 5 * B.natDegree < 7 * A.natDegree) :
    (n5QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  simp only [n5QuarticCostRestL810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestL810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestL810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestL810c5_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₅` is its unique top: every
load-free monomial costs more than `1·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN5CostTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F.natDegree + G.natDegree < 7 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 6 * A.natDegree ∧
    B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 6 * A.natDegree ∧
    B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree ∧
    B.natDegree + 2 * E.natDegree < 7 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 7 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree ∧
    3 * D.natDegree < 7 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 6 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 7 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 7 * A.natDegree ∧
    5 * B.natDegree < 7 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 1/4): 20 monomials. -/
def n5QuarticCostRestBeta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)
  + (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)
  - (7 / 2048 * beta : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 2/4): 20 monomials. -/
def n5QuarticCostRestBeta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(189 / 32768 * beta : k)) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)
  + (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 3/4): 20 monomials. -/
def n5QuarticCostRestBeta810c3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 4/4): 1 monomials. -/
def n5QuarticCostRestBeta810c4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
def n5QuarticCostRestBeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticCostRestBeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestBeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestBeta810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestBeta810c4 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₅` splits
into its pure-`A` `beta` column `c·beta·A^6` and the rest. -/
theorem degreeZeroN5Quartic810_eq_betaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 0 beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticBetaFace810 beta A +
        n5QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN5Quartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n5QuarticBetaFace810, n5QuarticCostRestBeta810, n5QuarticCostRestBeta810c1, n5QuarticCostRestBeta810c2, n5QuarticCostRestBeta810c3, n5QuarticCostRestBeta810c4,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestBeta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c1s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 4096) : k), (-(21 / 4096) : k), (5 / 512 : k),
      (5 / 256 : k), (5 / 128 : k), (135 / 1024 : k)
      ]
      [
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 0, 2, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c1s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c1s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c1s1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestBeta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c1s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (-(15 / 128) : k), (-(5 / 32) : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c1s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c1s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c1s2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestBeta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3
  + (5 / 16 : k) • (F * G)
  + (35 / 32768 * beta : k) • (A ^ 4 * C)
  - (21 / 131072 * beta : k) • (A ^ 3 * B ^ 2)
  + (35 / 8192 * beta : k) • (A ^ 3 * E)
  - (7 / 8192 * beta : k) • (A ^ 2 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c1s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (5 / 16 : k), (35 / 32768 * beta : k),
      (-(21 / 131072 * beta) : k), (35 / 8192 * beta : k), (-(7 / 8192 * beta) : k)
      ]
      [
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c1s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c1s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c1s3 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestBeta810c1`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (21 / 16384 * beta : k) • (A ^ 2 * C ^ 2)
  - (7 / 2048 * beta : k) • (A * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c1s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (21 / 16384 * beta : k), (-(7 / 2048 * beta) : k)
      ]
      [
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c1s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c1s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c1s4 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c1s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c1_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestBeta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestBeta810c1, n5QuarticCostRestBeta810c1s1, n5QuarticCostRestBeta810c1s2, n5QuarticCostRestBeta810c1s3, n5QuarticCostRestBeta810c1s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [n5QuarticCostRestBeta810c1_split 0 beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestBeta810c1s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestBeta810c1s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c1s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c1s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestBeta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(189 / 32768 * beta : k)) • B ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * G)
  - (7 / 512 * beta : k) • (A * B * F)
  + (7 / 1024 * beta : k) • (A * D ^ 2)
  + (35 / 1024 * beta : k) • (B ^ 2 * E)
  + (21 / 256 * beta : k) • (B * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c2s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(189 / 32768 * beta) : k), (21 / 1024 * beta : k), (-(7 / 512 * beta) : k),
      (7 / 1024 * beta : k), (35 / 1024 * beta : k), (21 / 256 * beta : k)
      ]
      [
      [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c2s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c2s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c2s1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestBeta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 512 * beta : k) • C ^ 3
  - (7 / 64 * beta : k) • (D * F)
  - (7 / 128 * beta : k) • E ^ 2
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c2s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 512 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (-(1 / 256 * gamma) : k), (9 / 128 * gamma : k), (9 / 128 * gamma : k)
      ]
      [
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c2s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c2s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c2s2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestBeta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 32 * gamma : k)) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (63 / 262144 * delta : k) • A ^ 5
  + (15 / 4096 * delta : k) • (A ^ 3 * C)
  - (5 / 16384 * delta : k) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c2s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 32 * gamma) : k), (-(3 / 16 * gamma) : k), (63 / 262144 * delta : k),
      (15 / 4096 * delta : k), (-(5 / 16384 * delta) : k), (15 / 1024 * delta : k)
      ]
      [
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c2s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c2s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c2s3 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestBeta810c2`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c2s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c2s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 * delta : k), (-(5 / 1024 * delta) : k)
      ]
      [
      [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c2s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c2s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c2s4 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c2s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestBeta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestBeta810c2, n5QuarticCostRestBeta810c2s1, n5QuarticCostRestBeta810c2s2, n5QuarticCostRestBeta810c2s3, n5QuarticCostRestBeta810c2s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [n5QuarticCostRestBeta810c2_split 0 beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestBeta810c2s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestBeta810c2s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c2s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c2s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestBeta810c3`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c3s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  + (1 / 32 * epsilon : k) • B ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c3s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c3s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 512 * delta : k), (5 / 64 * delta : k), (-(5 / 64 * delta) : k),
      (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k), (1 / 32 * epsilon : k)
      ]
      [
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c3s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c3s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c3s1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestBeta810c3`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c3s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c3s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c3s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k), (35 / 32768 * zeta : k),
      (3 / 256 * zeta : k), (3 / 1024 * zeta : k), (3 / 64 * zeta : k)
      ]
      [
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c3s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c3s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c3s2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestBeta810c3`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c3s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 64 * zeta : k)) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c3s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c3s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k),
      (-(3 / 32 * eta) : k), (1 / 4 * eta : k), (5 / 1024 * theta : k)
      ]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c3s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c3s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c3s3 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestBeta810c3`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestBeta810c3s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c3s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c3s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 32 * theta : k), (-(3 / 128 * theta) : k)
      ]
      [
      [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c3s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c3s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c3s4 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c3s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c3_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestBeta810c3s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c3s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c3s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestBeta810c3s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestBeta810c3, n5QuarticCostRestBeta810c3s1, n5QuarticCostRestBeta810c3s2, n5QuarticCostRestBeta810c3s3, n5QuarticCostRestBeta810c3s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c3 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [n5QuarticCostRestBeta810c3_split 0 beta gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestBeta810c3s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestBeta810c3s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c3s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c3s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestBeta810c4` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestBeta810c4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestBeta810c4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810c4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810c4 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestBeta810c4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestBeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp13 : 5 * B.natDegree < 6 * A.natDegree) :
    (n5QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  simp only [n5QuarticCostRestBeta810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestBeta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13) (n5QuarticCostRestBeta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13)) (n5QuarticCostRestBeta810c4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₅` is its unique top: every
load-free monomial costs more than `3·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN5CostTopBeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F.natDegree + G.natDegree < 6 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 5 * A.natDegree ∧
    B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 5 * A.natDegree ∧
    B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * E.natDegree < 6 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 6 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree ∧
    D.natDegree < 2 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 6 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 6 * A.natDegree ∧
    5 * B.natDegree < 6 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `delta` column, with the lighter
pure-`A` loads set to zero (chunk 1/3): 20 monomials. -/
def n5QuarticCostRestDelta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (15 / 4096 * delta : k) • (A ^ 3 * C)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `delta` column, with the lighter
pure-`A` loads set to zero (chunk 2/3): 20 monomials. -/
def n5QuarticCostRestDelta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16384 * delta : k)) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)
  - (5 / 64 * delta : k) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `delta` column, with the lighter
pure-`A` loads set to zero (chunk 3/3): 5 monomials. -/
def n5QuarticCostRestDelta810c3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
def n5QuarticCostRestDelta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticCostRestDelta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestDelta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestDelta810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₅` splits
into its pure-`A` `delta` column `c·delta·A^5` and the rest. -/
theorem degreeZeroN5Quartic810_eq_deltaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 0 0 gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticDeltaFace810 delta A +
        n5QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN5Quartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n5QuarticDeltaFace810, n5QuarticCostRestDelta810, n5QuarticCostRestDelta810c1, n5QuarticCostRestDelta810c2, n5QuarticCostRestDelta810c3,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestDelta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c1s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 4096) : k), (-(21 / 4096) : k), (5 / 512 : k),
      (5 / 256 : k), (5 / 128 : k), (135 / 1024 : k)
      ]
      [
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 0, 2, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c1s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c1s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c1s1 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestDelta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c1s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (-(15 / 128) : k), (-(5 / 32) : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c1s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c1s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c1s2 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestDelta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3
  + (5 / 16 : k) • (F * G)
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c1s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (5 / 16 : k), (-(1 / 256 * gamma) : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k)
      ]
      [
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c1s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c1s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c1s3 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestDelta810c1`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (D * E)
  + (15 / 4096 * delta : k) • (A ^ 3 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c1s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k), (15 / 4096 * delta : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0], [3, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c1s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c1s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c1s4 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c1s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c1_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestDelta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestDelta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestDelta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestDelta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestDelta810c1, n5QuarticCostRestDelta810c1s1, n5QuarticCostRestDelta810c1s2, n5QuarticCostRestDelta810c1s3, n5QuarticCostRestDelta810c1s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c1 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [n5QuarticCostRestDelta810c1_split 0 0 gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestDelta810c1s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18) (n5QuarticCostRestDelta810c1s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18)) (n5QuarticCostRestDelta810c1s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18)) (n5QuarticCostRestDelta810c1s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestDelta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16384 * delta : k)) • (A ^ 2 * B ^ 2)
  + (15 / 1024 * delta : k) • (A ^ 2 * E)
  + (5 / 512 * delta : k) • (A * B * D)
  - (5 / 1024 * delta : k) • (A * C ^ 2)
  + (45 / 512 * delta : k) • (B ^ 2 * C)
  + (5 / 64 * delta : k) • (A * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c2s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16384 * delta) : k), (15 / 1024 * delta : k), (5 / 512 * delta : k),
      (-(5 / 1024 * delta) : k), (45 / 512 * delta : k), (5 / 64 * delta : k)
      ]
      [
      [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n5QuarticCostRestDelta810c2s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c2s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c2s1 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestDelta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 64 * delta : k)) • (B * F)
  - (5 / 32 * delta : k) • (C * E)
  - (15 / 128 * delta : k) • D ^ 2
  + (1 / 32 * epsilon : k) • B ^ 3
  - (1 / 8 * epsilon : k) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c2s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 64 * delta) : k), (-(5 / 32 * delta) : k), (-(15 / 128 * delta) : k),
      (1 / 32 * epsilon : k), (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k)
      ]
      [
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c2s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c2s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c2s2 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestDelta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (35 / 32768 * zeta : k) • A ^ 4
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c2s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (35 / 32768 * zeta : k), (3 / 256 * zeta : k), (3 / 1024 * zeta : k),
      (3 / 64 * zeta : k), (-(9 / 64 * zeta) : k), (-(9 / 128 * zeta) : k)
      ]
      [
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c2s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c2s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c2s3 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestDelta810c2`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestDelta810c2s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c2s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * zeta : k), (-(3 / 32 * eta) : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c2s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c2s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c2s4 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c2s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestDelta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestDelta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestDelta810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestDelta810c2s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestDelta810c2, n5QuarticCostRestDelta810c2s1, n5QuarticCostRestDelta810c2s2, n5QuarticCostRestDelta810c2s3, n5QuarticCostRestDelta810c2s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c2 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [n5QuarticCostRestDelta810c2_split 0 0 gamma delta epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestDelta810c2s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18) (n5QuarticCostRestDelta810c2s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18)) (n5QuarticCostRestDelta810c2s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18)) (n5QuarticCostRestDelta810c2s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18))

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestDelta810c3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestDelta810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 4 * eta : k), (5 / 1024 * theta : k), (1 / 32 * theta : k),
      (-(3 / 128 * theta) : k), (1 / 8 * theta : k)
      ]
      [
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestDelta810c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810c3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810c3 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestDelta810c3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestDelta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp8 : 3 * D.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp13 : B.natDegree < A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : 3 * B.natDegree < 4 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n5QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  simp only [n5QuarticCostRestDelta810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestDelta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18) (n5QuarticCostRestDelta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18)) (n5QuarticCostRestDelta810c3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₅` is its unique top: every
load-free monomial costs more than `5·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN5CostTopDelta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F.natDegree + G.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 4 * A.natDegree ∧
    B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 4 * A.natDegree ∧
    B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * E.natDegree < 5 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 5 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree ∧
    3 * D.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 5 * A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C.natDegree + F.natDegree < 5 * A.natDegree ∧
    D.natDegree + E.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `zeta` column, with the lighter
pure-`A` loads set to zero (chunk 1/2): 20 monomials. -/
def n5QuarticCostRestZeta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (1 / 32 * epsilon : k) • B ^ 3

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `zeta` column, with the lighter
pure-`A` loads set to zero (chunk 2/2): 14 monomials. -/
def n5QuarticCostRestZeta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)
  - (9 / 128 * zeta : k) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
def n5QuarticCostRestZeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticCostRestZeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestZeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₅` splits
into its pure-`A` `zeta` column `c·zeta·A^4` and the rest. -/
theorem degreeZeroN5Quartic810_eq_zetaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G =
      n5QuarticZetaFace810 zeta A +
        n5QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN5Quartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n5QuarticZetaFace810, n5QuarticCostRestZeta810, n5QuarticCostRestZeta810c1, n5QuarticCostRestZeta810c2,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestZeta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c1s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 4096) : k), (-(21 / 4096) : k), (5 / 512 : k),
      (5 / 256 : k), (5 / 128 : k), (135 / 1024 : k)
      ]
      [
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 0, 2, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c1s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c1s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c1s1 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestZeta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c1s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (-(15 / 128) : k), (-(5 / 32) : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c1s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c1s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c1s2 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestZeta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3
  + (5 / 16 : k) • (F * G)
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c1s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (5 / 16 : k), (-(1 / 256 * gamma) : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k)
      ]
      [
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c1s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c1s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c1s3 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestZeta810c1`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (D * E)
  + (1 / 32 * epsilon : k) • B ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c1s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k), (1 / 32 * epsilon : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c1s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c1s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c1s4 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c1s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c1_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestZeta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestZeta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestZeta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestZeta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestZeta810c1, n5QuarticCostRestZeta810c1s1, n5QuarticCostRestZeta810c1s2, n5QuarticCostRestZeta810c1s3, n5QuarticCostRestZeta810c1s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c1 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [n5QuarticCostRestZeta810c1_split 0 0 gamma 0 epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestZeta810c1s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21) (n5QuarticCostRestZeta810c1s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21)) (n5QuarticCostRestZeta810c1s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21)) (n5QuarticCostRestZeta810c1s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/3 of `n5QuarticCostRestZeta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  + (3 / 256 * zeta : k) • (A ^ 2 * C)
  + (3 / 1024 * zeta : k) • (A * B ^ 2)
  + (3 / 64 * zeta : k) • (A * E)
  - (9 / 64 * zeta : k) • (B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c2s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k), (3 / 256 * zeta : k),
      (3 / 1024 * zeta : k), (3 / 64 * zeta : k), (-(9 / 64 * zeta) : k)
      ]
      [
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c2s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c2s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c2s1 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c2s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/3 of `n5QuarticCostRestZeta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(9 / 128 * zeta : k)) • C ^ 2
  + (3 / 8 * zeta : k) • G
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (5 / 1024 * theta : k) • A ^ 3
  + (1 / 32 * theta : k) • (A * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c2s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * zeta) : k), (3 / 8 * zeta : k), (-(3 / 32 * eta) : k),
      (1 / 4 * eta : k), (5 / 1024 * theta : k), (1 / 32 * theta : k)
      ]
      [
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c2s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c2s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c2s2 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c2s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/3 of `n5QuarticCostRestZeta810c2`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestZeta810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 128 * theta : k)) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestZeta810c2s3` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c2s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 128 * theta) : k), (1 / 8 * theta : k)
      ]
      [
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestZeta810c2s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c2s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c2s3 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestZeta810c2s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestZeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestZeta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestZeta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestZeta810c2s3 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestZeta810c2, n5QuarticCostRestZeta810c2s1, n5QuarticCostRestZeta810c2s2, n5QuarticCostRestZeta810c2s3]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810c2 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [n5QuarticCostRestZeta810c2_split 0 0 gamma 0 epsilon zeta eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestZeta810c2s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21) (n5QuarticCostRestZeta810c2s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21)) (n5QuarticCostRestZeta810c2s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21))

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestZeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp8 : 3 * D.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp13 : 5 * B.natDegree < 4 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree < A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp21 : 3 * B.natDegree < 4 * A.natDegree) :
    (n5QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  simp only [n5QuarticCostRestZeta810]
  exact (natDegree_add_lt810 (n5QuarticCostRestZeta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21) (n5QuarticCostRestZeta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₅` is its unique top: every
load-free monomial costs more than `7·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN5CostTopZeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F.natDegree + G.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 3 * A.natDegree ∧
    B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 3 * A.natDegree ∧
    B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * E.natDegree < 4 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree ∧
    3 * D.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 3 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 4 * A.natDegree ∧
    5 * B.natDegree < 4 * A.natDegree ∧
    C.natDegree + F.natDegree < 4 * A.natDegree ∧
    D.natDegree + E.natDegree < 4 * A.natDegree ∧
    B.natDegree < A.natDegree ∧
    2 * B.natDegree + D.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 4 * A.natDegree ∧
    B.natDegree + E.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree < 4 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `theta` column, with the lighter
pure-`A` loads set to zero (chunk 1/2): 20 monomials. -/
def n5QuarticCostRestTheta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)
  + (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)
  - (5 / 128 : k) • D ^ 3
  + (5 / 16 : k) • (F * G)
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)
  - (3 / 16 * gamma : k) • (D * E)
  + (1 / 32 * epsilon : k) • B ^ 3

set_option maxHeartbeats 64000000 in
/-- `N₅` off its pure-`A` `theta` column, with the lighter
pure-`A` loads set to zero (chunk 2/2): 7 monomials. -/
def n5QuarticCostRestTheta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2
  + (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
def n5QuarticCostRestTheta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n5QuarticCostRestTheta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n5QuarticCostRestTheta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₅` splits
into its pure-`A` `theta` column `c·theta·A^3` and the rest. -/
theorem degreeZeroN5Quartic810_eq_thetaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN5Quartic810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G =
      n5QuarticThetaFace810 theta A +
        n5QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G := by
  simp only [degreeZeroN5Quartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n5QuarticThetaFace810, n5QuarticCostRestTheta810, n5QuarticCostRestTheta810c1, n5QuarticCostRestTheta810c2,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/4 of `n5QuarticCostRestTheta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestTheta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 4096 : k)) • (A * B ^ 3 * C)
  - (21 / 4096 : k) • B ^ 5
  + (5 / 512 : k) • (A * B ^ 2 * F)
  + (5 / 256 : k) • (A * B * D ^ 2)
  + (5 / 128 : k) • (B ^ 3 * E)
  + (135 / 1024 : k) • (B ^ 2 * C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestTheta810c1s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 4096) : k), (-(21 / 4096) : k), (5 / 512 : k),
      (5 / 256 : k), (5 / 128 : k), (135 / 1024 : k)
      ]
      [
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 0, 2, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestTheta810c1s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c1s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c1s1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/4 of `n5QuarticCostRestTheta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestTheta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 1024 : k) • (B * C ^ 3)
  - (15 / 128 : k) • (B * C * G)
  - (5 / 32 : k) • (B * D * F)
  - (5 / 64 : k) • (B * E ^ 2)
  - (5 / 64 : k) • (C ^ 2 * F)
  - (25 / 128 : k) • (C * D * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestTheta810c1s2` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 1024 : k), (-(15 / 128) : k), (-(5 / 32) : k),
      (-(5 / 64) : k), (-(5 / 64) : k), (-(25 / 128) : k)
      ]
      [
      [0, 1, 3, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestTheta810c1s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c1s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c1s2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 3/4 of `n5QuarticCostRestTheta810c1`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestTheta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • D ^ 3
  + (5 / 16 : k) • (F * G)
  - (1 / 256 * gamma : k) • (A * B ^ 3)
  + (9 / 128 * gamma : k) • (B ^ 2 * D)
  + (9 / 128 * gamma : k) • (B * C ^ 2)
  - (3 / 32 * gamma : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestTheta810c1s3` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128) : k), (5 / 16 : k), (-(1 / 256 * gamma) : k),
      (9 / 128 * gamma : k), (9 / 128 * gamma : k), (-(3 / 32 * gamma) : k)
      ]
      [
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [n5QuarticCostRestTheta810c1s3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c1s3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c1s3 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 4/4 of `n5QuarticCostRestTheta810c1`
(2 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestTheta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (D * E)
  + (1 / 32 * epsilon : k) • B ^ 3

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestTheta810c1s4` (2 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k), (1 / 32 * epsilon : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0], [0, 3, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestTheta810c1s4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c1s4_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c1s4 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c1s4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c1_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestTheta810c1s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestTheta810c1s2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestTheta810c1s3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestTheta810c1s4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestTheta810c1, n5QuarticCostRestTheta810c1s1, n5QuarticCostRestTheta810c1s2, n5QuarticCostRestTheta810c1s3, n5QuarticCostRestTheta810c1s4]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [n5QuarticCostRestTheta810c1_split 0 0 gamma 0 epsilon 0 eta theta A B C D E F G]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n5QuarticCostRestTheta810c1s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23) (n5QuarticCostRestTheta810c1s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23)) (n5QuarticCostRestTheta810c1s3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23)) (n5QuarticCostRestTheta810c1s4_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23))

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 1/2 of `n5QuarticCostRestTheta810c2`
(6 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestTheta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(1 / 8 * epsilon : k)) • (B * E)
  - (3 / 16 * epsilon : k) • (C * D)
  - (3 / 32 * eta : k) • (B * C)
  + (1 / 4 * eta : k) • F
  + (1 / 32 * theta : k) • (A * C)
  - (3 / 128 * theta : k) • B ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestTheta810c2s1` (6 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c2s1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 8 * epsilon) : k), (-(3 / 16 * epsilon) : k), (-(3 / 32 * eta) : k),
      (1 / 4 * eta : k), (1 / 32 * theta : k), (-(3 / 128 * theta) : k)
      ]
      [
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0]
      ] := by
  simp only [n5QuarticCostRestTheta810c2s1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c2s1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c2s1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c2s1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Sub-chunk 2/2 of `n5QuarticCostRestTheta810c2`
(1 monomials): a `compute_degree` over more than six
monomials with seven symbolic degrees times out. -/
def n5QuarticCostRestTheta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 8 * theta : k) • E

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n5QuarticCostRestTheta810c2s2` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c2s2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 8 * theta : k)
      ]
      [
      [0, 0, 0, 0, 1, 0, 0]
      ] := by
  simp only [n5QuarticCostRestTheta810c2s2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c2s2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c2s2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [refl810PolyOf_ChamberN5CostLadder_n5QuarticCostRestTheta810c2s2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c2_split
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n5QuarticCostRestTheta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n5QuarticCostRestTheta810c2s1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n5QuarticCostRestTheta810c2s2 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n5QuarticCostRestTheta810c2, n5QuarticCostRestTheta810c2s1, n5QuarticCostRestTheta810c2s2]
  all_goals module

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810c2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [n5QuarticCostRestTheta810c2_split 0 0 gamma 0 epsilon 0 eta theta A B C D E F G]
  exact (natDegree_add_lt810 (n5QuarticCostRestTheta810c2s1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23) (n5QuarticCostRestTheta810c2s2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23))

set_option maxHeartbeats 64000000 in
theorem n5QuarticCostRestTheta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : F.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp8 : D.natDegree < A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp13 : 5 * B.natDegree < 3 * A.natDegree)
    (hp14 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp15 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp16 : 3 * B.natDegree < 2 * A.natDegree)
    (hp17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp19 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp20 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp21 : B.natDegree < A.natDegree)
    (hp22 : F.natDegree < 3 * A.natDegree)
    (hp23 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n5QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  simp only [n5QuarticCostRestTheta810]
  exact (natDegree_add_lt810 (n5QuarticCostRestTheta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23) (n5QuarticCostRestTheta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `theta` column of `N₅` is its unique top: every
load-free monomial costs more than `9·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN5CostTopTheta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    F.natDegree + G.natDegree < 3 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 2 * A.natDegree ∧
    B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 2 * A.natDegree ∧
    B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree ∧
    B.natDegree + 2 * E.natDegree < 3 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 3 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree ∧
    D.natDegree < A.natDegree ∧
    3 * B.natDegree + C.natDegree < 2 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 3 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 3 * A.natDegree ∧
    5 * B.natDegree < 3 * A.natDegree ∧
    C.natDegree + F.natDegree < 3 * A.natDegree ∧
    D.natDegree + E.natDegree < 3 * A.natDegree ∧
    3 * B.natDegree < 2 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 3 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 3 * A.natDegree ∧
    B.natDegree + E.natDegree < 3 * A.natDegree ∧
    C.natDegree + D.natDegree < 3 * A.natDegree ∧
    B.natDegree < A.natDegree ∧
    F.natDegree < 3 * A.natDegree ∧
    B.natDegree + C.natDegree < 3 * A.natDegree

/-! ### `N₅` cost-form monotonicity, kills and bands -/

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `N₅` tops it only if the cheaper `l`
column does. -/
theorem quarticN5CostTopBeta810_imp_L810
    {A B C D E F G : k[X]}
    (h : QuarticN5CostTopBeta810 A B C D E F G) :
    QuarticN5CostTopL810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `N₅` tops it only if the cheaper `beta`
column does. -/
theorem quarticN5CostTopDelta810_imp_Beta810
    {A B C D E F G : k[X]}
    (h : QuarticN5CostTopDelta810 A B C D E F G) :
    QuarticN5CostTopBeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `N₅` tops it only if the cheaper `delta`
column does. -/
theorem quarticN5CostTopZeta810_imp_Delta810
    {A B C D E F G : k[X]}
    (h : QuarticN5CostTopZeta810 A B C D E F G) :
    QuarticN5CostTopDelta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `N₅` tops it only if the cheaper `zeta`
column does. -/
theorem quarticN5CostTopTheta810_imp_Zeta810
    {A B C D E F G : k[X]}
    (h : QuarticN5CostTopTheta810 A B C D E F G) :
    QuarticN5CostTopZeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `l` column tops `N₅` then
`l = 0`, because `natDegree N₅ ≤ 2·a < 7·a`. -/
theorem quarticSigmaN5Cost_l_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN5CostTopL810 A B C D E F G)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    l = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (429 / 33554432 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n5QuarticLFace810 l A).natDegree = 7 * A.natDegree := by
    simp only [n5QuarticLFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n5QuarticCostRestL810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13
  have hle := degreeZeroN5Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_lCostColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `beta` column tops `N₅` then
`beta = 0`, because `natDegree N₅ ≤ 2·a < 6·a`. -/
theorem quarticSigmaN5Cost_beta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN5CostTopBeta810 A B C D E F G)
    (hl0 : l = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    beta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (231 / 4194304 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n5QuarticBetaFace810 beta A).natDegree = 6 * A.natDegree := by
    simp only [n5QuarticBetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n5QuarticCostRestBeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13
  subst hl0
  have hle := degreeZeroN5Quartic810_natDegree_le 0 beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_betaCostColumn_add_rest (l := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `delta` column tops `N₅` then
`delta = 0`, because `natDegree N₅ ≤ 2·a < 5·a`. -/
theorem quarticSigmaN5Cost_delta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN5CostTopDelta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    delta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (63 / 262144 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n5QuarticDeltaFace810 delta A).natDegree = 5 * A.natDegree := by
    simp only [n5QuarticDeltaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n5QuarticCostRestDelta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18
  subst hl0
  subst hbeta0
  have hle := degreeZeroN5Quartic810_natDegree_le 0 0 gamma delta epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_deltaCostColumn_add_rest (l := 0) (beta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `zeta` column tops `N₅` then
`zeta = 0`, because `natDegree N₅ ≤ 2·a < 4·a`. -/
theorem quarticSigmaN5Cost_zeta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN5CostTopZeta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    zeta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (35 / 32768 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n5QuarticZetaFace810 zeta A).natDegree = 4 * A.natDegree := by
    simp only [n5QuarticZetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n5QuarticCostRestZeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21
  subst hl0
  subst hbeta0
  subst hdelta0
  have hle := degreeZeroN5Quartic810_natDegree_le 0 0 gamma 0 epsilon zeta eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_zetaCostColumn_add_rest (l := 0) (beta := 0) (delta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `theta` column tops `N₅` then
`theta = 0`, because `natDegree N₅ ≤ 2·a < 3·a`. -/
theorem quarticSigmaN5Cost_theta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN5CostTopTheta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    theta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (5 / 1024 * theta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n5QuarticThetaFace810 theta A).natDegree = 3 * A.natDegree := by
    simp only [n5QuarticThetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n5QuarticCostRestTheta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23
  subst hl0
  subst hbeta0
  subst hdelta0
  subst hzeta0
  have hle := degreeZeroN5Quartic810_natDegree_le 0 0 gamma 0 epsilon 0 eta theta
    A B C D E F G hApos homi hnu hkap
  rw [degreeZeroN5Quartic810_eq_thetaCostColumn_add_rest (l := 0) (beta := 0) (delta := 0) (zeta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN5Cost_l_band
    {l : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN5CostTopL810 A B C D E F G → l = 0) :
    l = 0 ∨
      7 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      7 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ 3 * D.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      7 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      7 * A.natDegree ≤ 5 * B.natDegree := by
  by_cases hb0 : F.natDegree + G.natDegree < 7 * A.natDegree
  · by_cases hb1 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree
    · by_cases hb2 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree
      · by_cases hb3 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree
        · by_cases hb4 : B.natDegree + D.natDegree + F.natDegree < 7 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * E.natDegree < 7 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree
              · by_cases hb7 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree
                · by_cases hb8 : 3 * D.natDegree < 7 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree
                      · by_cases hb11 : 2 * B.natDegree + C.natDegree + D.natDegree < 7 * A.natDegree
                        · by_cases hb12 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree
                          · by_cases hb13 : 5 * B.natDegree < 7 * A.natDegree
                            · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13⟩)
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN5Cost_beta_band
    {beta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN5CostTopBeta810 A B C D E F G → beta = 0) :
    beta = 0 ∨
      6 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ D.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      6 * A.natDegree ≤ 5 * B.natDegree := by
  by_cases hb0 : F.natDegree + G.natDegree < 6 * A.natDegree
  · by_cases hb1 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree
    · by_cases hb2 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree
      · by_cases hb3 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree
        · by_cases hb4 : B.natDegree + D.natDegree + F.natDegree < 6 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * E.natDegree < 6 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree
              · by_cases hb7 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree
                · by_cases hb8 : D.natDegree < 2 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree
                      · by_cases hb11 : 2 * B.natDegree + C.natDegree + D.natDegree < 6 * A.natDegree
                        · by_cases hb12 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree
                          · by_cases hb13 : 5 * B.natDegree < 6 * A.natDegree
                            · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13⟩)
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN5Cost_delta_band
    {delta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN5CostTopDelta810 A B C D E F G → delta = 0) :
    delta = 0 ∨
      5 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 3 * D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree := by
  by_cases hb0 : F.natDegree + G.natDegree < 5 * A.natDegree
  · by_cases hb1 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree
    · by_cases hb2 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree
      · by_cases hb3 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree
        · by_cases hb4 : B.natDegree + D.natDegree + F.natDegree < 5 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * E.natDegree < 5 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree
              · by_cases hb7 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree
                · by_cases hb8 : 3 * D.natDegree < 5 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree
                      · by_cases hb11 : 2 * B.natDegree + C.natDegree + D.natDegree < 5 * A.natDegree
                        · by_cases hb12 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree
                          · by_cases hb13 : B.natDegree < A.natDegree
                            · by_cases hb14 : C.natDegree + F.natDegree < 5 * A.natDegree
                              · by_cases hb15 : D.natDegree + E.natDegree < 5 * A.natDegree
                                · by_cases hb16 : 3 * B.natDegree < 4 * A.natDegree
                                  · by_cases hb17 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree
                                    · by_cases hb18 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree
                                      · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18⟩)
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN5Cost_zeta_band
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN5CostTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      4 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * D.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      4 * A.natDegree ≤ 5 * B.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree := by
  by_cases hb0 : F.natDegree + G.natDegree < 4 * A.natDegree
  · by_cases hb1 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree
    · by_cases hb2 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree
      · by_cases hb3 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree
        · by_cases hb4 : B.natDegree + D.natDegree + F.natDegree < 4 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * E.natDegree < 4 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree
              · by_cases hb7 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree
                · by_cases hb8 : 3 * D.natDegree < 4 * A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree
                      · by_cases hb11 : 2 * B.natDegree + C.natDegree + D.natDegree < 4 * A.natDegree
                        · by_cases hb12 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree
                          · by_cases hb13 : 5 * B.natDegree < 4 * A.natDegree
                            · by_cases hb14 : C.natDegree + F.natDegree < 4 * A.natDegree
                              · by_cases hb15 : D.natDegree + E.natDegree < 4 * A.natDegree
                                · by_cases hb16 : B.natDegree < A.natDegree
                                  · by_cases hb17 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree
                                    · by_cases hb18 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree
                                      · by_cases hb19 : B.natDegree + E.natDegree < 4 * A.natDegree
                                        · by_cases hb20 : C.natDegree + D.natDegree < 4 * A.natDegree
                                          · by_cases hb21 : 3 * B.natDegree < 4 * A.natDegree
                                            · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21⟩)
                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))))))))))
                                              omega
                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))
                                            omega
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN5Cost_theta_band
    {theta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN5CostTopTheta810 A B C D E F G → theta = 0) :
    theta = 0 ∨
      3 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      3 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      A.natDegree ≤ D.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      3 * A.natDegree ≤ 5 * B.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      3 * A.natDegree ≤ F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree := by
  by_cases hb0 : F.natDegree + G.natDegree < 3 * A.natDegree
  · by_cases hb1 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree
    · by_cases hb2 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree
      · by_cases hb3 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree
        · by_cases hb4 : B.natDegree + D.natDegree + F.natDegree < 3 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * E.natDegree < 3 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree
              · by_cases hb7 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree
                · by_cases hb8 : D.natDegree < A.natDegree
                  · by_cases hb9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree
                      · by_cases hb11 : 2 * B.natDegree + C.natDegree + D.natDegree < 3 * A.natDegree
                        · by_cases hb12 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree
                          · by_cases hb13 : 5 * B.natDegree < 3 * A.natDegree
                            · by_cases hb14 : C.natDegree + F.natDegree < 3 * A.natDegree
                              · by_cases hb15 : D.natDegree + E.natDegree < 3 * A.natDegree
                                · by_cases hb16 : 3 * B.natDegree < 2 * A.natDegree
                                  · by_cases hb17 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree
                                    · by_cases hb18 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree
                                      · by_cases hb19 : B.natDegree + E.natDegree < 3 * A.natDegree
                                        · by_cases hb20 : C.natDegree + D.natDegree < 3 * A.natDegree
                                          · by_cases hb21 : B.natDegree < A.natDegree
                                            · by_cases hb22 : F.natDegree < 3 * A.natDegree
                                              · by_cases hb23 : B.natDegree + C.natDegree < 3 * A.natDegree
                                                · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23⟩)
                                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))))))))))))))))))
                                                  omega
                                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))))
                                                omega
                                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))))
                                              omega
                                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))))
                                            omega
                                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))))
                                          omega
                                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))))
                                        omega
                                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))))
                                      omega
                                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))))
                                    omega
                                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))))
                                  omega
                              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))))
                                omega
                            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
                              omega
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))))
                            omega
                        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))
                          omega
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
                        omega
                    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
                      omega
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))
                    omega
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
                  omega
              · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
                omega
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
              omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            omega
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          omega
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        omega
    · refine Or.inr (Or.inr (Or.inl ?_))
      omega
  · refine Or.inr (Or.inl ?_)
    omega

set_option maxHeartbeats 64000000 in
/-- The cost-form `N₅` ladder as five band disjunctions. -/
theorem quarticSigmaN5CostBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    (l = 0 ∨
      7 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      7 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      7 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ 3 * D.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      7 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      7 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      7 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      7 * A.natDegree ≤ 5 * B.natDegree) ∧
    (beta = 0 ∨
      6 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ D.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      6 * A.natDegree ≤ 5 * B.natDegree) ∧
    (delta = 0 ∨
      5 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 3 * D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree) ∧
    (zeta = 0 ∨
      4 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * D.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      4 * A.natDegree ≤ 5 * B.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree) ∧
    (theta = 0 ∨
      3 * A.natDegree ≤ F.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + D.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * E.natDegree ∨
      3 * A.natDegree ≤ 2 * C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree + E.natDegree ∨
      A.natDegree ≤ D.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + C.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 3 * C.natDegree ∨
      3 * A.natDegree ≤ 5 * B.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      3 * A.natDegree ≤ F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree) := by
  by_cases hTl : QuarticN5CostTopL810 A B C D E F G
  · have hl0 : l = 0 :=
      quarticSigmaN5Cost_l_eq_zero l beta gamma delta epsilon zeta eta theta
        A B C D E F G hTl homi hnu hkap
    by_cases hTbeta : QuarticN5CostTopBeta810 A B C D E F G
    · have hbeta0 : beta = 0 :=
        quarticSigmaN5Cost_beta_eq_zero l beta gamma delta epsilon zeta eta theta
          A B C D E F G hTbeta hl0 homi hnu hkap
      by_cases hTdelta : QuarticN5CostTopDelta810 A B C D E F G
      · have hdelta0 : delta = 0 :=
          quarticSigmaN5Cost_delta_eq_zero l beta gamma delta epsilon zeta eta theta
            A B C D E F G hTdelta hl0 hbeta0 homi hnu hkap
        by_cases hTzeta : QuarticN5CostTopZeta810 A B C D E F G
        · have hzeta0 : zeta = 0 :=
            quarticSigmaN5Cost_zeta_eq_zero l beta gamma delta epsilon zeta eta theta
              A B C D E F G hTzeta hl0 hbeta0 hdelta0 homi hnu hkap
          by_cases hTtheta : QuarticN5CostTopTheta810 A B C D E F G
          · have htheta0 : theta = 0 :=
              quarticSigmaN5Cost_theta_eq_zero l beta gamma delta epsilon zeta eta theta
                A B C D E F G hTtheta hl0 hbeta0 hdelta0 hzeta0 homi hnu hkap
            exact ⟨Or.inl hl0, Or.inl hbeta0, Or.inl hdelta0, Or.inl hzeta0, Or.inl htheta0⟩
          · exact ⟨Or.inl hl0,
              Or.inl hbeta0,
              Or.inl hdelta0,
              Or.inl hzeta0,
              quarticSigmaN5Cost_theta_band (theta := theta) A B C D E F G hA
                (fun htop => absurd (htop) hTtheta)⟩
        · exact ⟨Or.inl hl0,
            Or.inl hbeta0,
            Or.inl hdelta0,
            quarticSigmaN5Cost_zeta_band (zeta := zeta) A B C D E F G hA
              (fun htop => absurd (htop) hTzeta),
            quarticSigmaN5Cost_theta_band (theta := theta) A B C D E F G hA
              (fun htop => absurd (quarticN5CostTopTheta810_imp_Zeta810 (htop)) hTzeta)⟩
      · exact ⟨Or.inl hl0,
          Or.inl hbeta0,
          quarticSigmaN5Cost_delta_band (delta := delta) A B C D E F G hA
            (fun htop => absurd (htop) hTdelta),
          quarticSigmaN5Cost_zeta_band (zeta := zeta) A B C D E F G hA
            (fun htop => absurd (quarticN5CostTopZeta810_imp_Delta810 (htop)) hTdelta),
          quarticSigmaN5Cost_theta_band (theta := theta) A B C D E F G hA
            (fun htop => absurd (quarticN5CostTopZeta810_imp_Delta810 (quarticN5CostTopTheta810_imp_Zeta810 (htop))) hTdelta)⟩
    · exact ⟨Or.inl hl0,
        quarticSigmaN5Cost_beta_band (beta := beta) A B C D E F G hA
          (fun htop => absurd (htop) hTbeta),
        quarticSigmaN5Cost_delta_band (delta := delta) A B C D E F G hA
          (fun htop => absurd (quarticN5CostTopDelta810_imp_Beta810 (htop)) hTbeta),
        quarticSigmaN5Cost_zeta_band (zeta := zeta) A B C D E F G hA
          (fun htop => absurd (quarticN5CostTopDelta810_imp_Beta810 (quarticN5CostTopZeta810_imp_Delta810 (htop))) hTbeta),
        quarticSigmaN5Cost_theta_band (theta := theta) A B C D E F G hA
          (fun htop => absurd (quarticN5CostTopDelta810_imp_Beta810 (quarticN5CostTopZeta810_imp_Delta810 (quarticN5CostTopTheta810_imp_Zeta810 (htop)))) hTbeta)⟩
  · exact ⟨quarticSigmaN5Cost_l_band (l := l) A B C D E F G hA
        (fun htop => absurd (htop) hTl),
      quarticSigmaN5Cost_beta_band (beta := beta) A B C D E F G hA
        (fun htop => absurd (quarticN5CostTopBeta810_imp_L810 (htop)) hTl),
      quarticSigmaN5Cost_delta_band (delta := delta) A B C D E F G hA
        (fun htop => absurd (quarticN5CostTopBeta810_imp_L810 (quarticN5CostTopDelta810_imp_Beta810 (htop))) hTl),
      quarticSigmaN5Cost_zeta_band (zeta := zeta) A B C D E F G hA
        (fun htop => absurd (quarticN5CostTopBeta810_imp_L810 (quarticN5CostTopDelta810_imp_Beta810 (quarticN5CostTopZeta810_imp_Delta810 (htop)))) hTl),
      quarticSigmaN5Cost_theta_band (theta := theta) A B C D E F G hA
        (fun htop => absurd (quarticN5CostTopBeta810_imp_L810 (quarticN5CostTopDelta810_imp_Beta810 (quarticN5CostTopZeta810_imp_Delta810 (quarticN5CostTopTheta810_imp_Zeta810 (htop))))) hTl)⟩


end QuarticCostLadderN5810

end Max11DegreeRoutes
