import Grok810ScaleZeroQuarticTowerSpeedTPart03Scratch

/-! # The `N₇` cost ladder — the split the 202 wall kills need

`Grok810ScaleZeroQuarticTowerScratch` proves
`quarticSigma_<load>_eq_zero_of_N7_column` with the module identity
`N₇ = face + rest` and the rest bound as *hypotheses* ("the module
identity unfolds `Π` and lives in the residual assembly").  This module
supplies exactly those: `N₇` off its five pure-`A` load columns (chunked
at 20 monomials), the one heavy split identity through the eight `rho`
groups, the cost-form `Top` predicates (one inequality per minimal
load-free monomial of `N₇`, plus one per minimal monomial of each lighter
`γ/ε/η` column), the rest bounds, and the five kills.  Every rest
monomial is Farkas-checked against its predicate in
`scripts/check_810_quartic_chambers_lean.py`.  Untracked working note.
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

section QuarticN7Ladder810

/-! ## `N₇` off its five pure-`A` load columns -/

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 1/7: 20 monomials. -/
def n7QuarticNoPureA1810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * B ^ 3 * C)
  + (23 / 8192 : k) • (A * B ^ 5)
  - (5 / 512 : k) • (A * B ^ 3 * E)
  + (15 / 512 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 64 : k) • (A * B * C * G)
  - (5 / 64 : k) • (A * C ^ 2 * F)
  - (5 / 64 : k) • (A * C * D * E)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 2/7: 20 monomials. -/
def n7QuarticNoPureA2810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (D * E ^ 2)
  + (315 / 524288 * l : k) • (A ^ 6 * C)
  - (315 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (315 / 131072 * l : k) • (A ^ 5 * E)
  - (315 / 262144 * l : k) • (A ^ 4 * B * D)
  + (1485 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (63 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  - (45 / 524288 * l : k) • (A ^ 2 * B ^ 4)
  + (315 / 32768 * l : k) • (A ^ 4 * G)
  - (45 / 8192 * l : k) • (A ^ 3 * B * F)
  + (171 / 8192 * l : k) • (A ^ 3 * C * E)
  - (45 / 16384 * l : k) • (A ^ 3 * D ^ 2)
  - (45 / 16384 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C * D)
  - (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)
  - (27 / 4096 * l : k) • (A * B ^ 3 * D)
  + (45 / 4096 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 128 * l : k) • (A ^ 2 * C * G)
  - (27 / 1024 * l : k) • (A ^ 2 * D * F)

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 3/7: 20 monomials. -/
def n7QuarticNoPureA3810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (81 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  - (9 / 512 * l : k) • (A * B ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * C * F)
  - (9 / 256 * l : k) • (A * C ^ 2 * E)
  - (9 / 512 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 32 * l : k) • (A * E * G)
  - (9 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (35 / 16384 * beta : k) • (A ^ 5 * C)

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 4/7: 20 monomials. -/
def n7QuarticNoPureA4810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 65536 * beta : k)) • (A ^ 4 * B ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 4 * E)
  - (35 / 8192 * beta : k) • (A ^ 3 * B * D)
  + (91 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  - (35 / 16384 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (49 / 32768 * beta : k) • (A * B ^ 4)
  + (35 / 1024 * beta : k) • (A ^ 3 * G)
  - (21 / 1024 * beta : k) • (A ^ 2 * B * F)
  + (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  - (21 / 2048 * beta : k) • (A ^ 2 * D ^ 2)
  - (7 / 1024 * beta : k) • (A * B ^ 2 * E)
  + (7 / 256 * beta : k) • (A * B * C * D)
  + (7 / 512 * beta : k) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  - (7 / 64 * beta : k) • (A * D * F)
  + (7 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 5/7: 20 monomials. -/
def n7QuarticNoPureA5810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 64 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 16 * gamma : k) • (A * C * F)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)
  + (15 / 2048 * delta : k) • (A ^ 4 * C)
  - (15 / 8192 * delta : k) • (A ^ 3 * B ^ 2)
  + (15 / 512 * delta : k) • (A ^ 3 * E)
  - (15 / 1024 * delta : k) • (A ^ 2 * B * D)
  + (5 / 2048 * delta : k) • (A ^ 2 * C ^ 2)
  + (25 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (15 / 128 * delta : k) • (A ^ 2 * G)
  - (5 / 64 * delta : k) • (A * B * F)
  - (5 / 64 * delta : k) • (A * C * E)

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 6/7: 20 monomials. -/
def n7QuarticNoPureA6810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 * delta : k)) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2
  - (1 / 8 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)
  + (3 / 128 * zeta : k) • (A ^ 3 * C)
  - (3 / 512 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A ^ 2 * E)
  - (3 / 64 * zeta : k) • (A * B * D)
  - (9 / 128 * zeta : k) • (A * C ^ 2)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)

set_option maxHeartbeats 64000000 in
/-- `N₇` off its pure-`A` load columns, chunk 7/7: 11 monomials. -/
def n7QuarticNoPureA7810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * zeta : k)) • D ^ 2
  - (1 / 16 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)
  + (1 / 16 * theta : k) • (A ^ 2 * C)
  - (1 / 64 * theta : k) • (A * B ^ 2)
  + (1 / 4 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
def n7QuarticNoPureA810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticNoPureA1810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n7QuarticNoPureA2810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n7QuarticNoPureA3810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n7QuarticNoPureA4810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n7QuarticNoPureA5810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n7QuarticNoPureA6810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n7QuarticNoPureA7810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: `N₇` splits into its five pure-`A` load columns and
the rest.  This is the module identity the tower lane's
`quarticSigma_<load>_eq_zero_of_N7_column` takes as a hypothesis;
it unfolds `Π` through the eight `rho` groups. -/
theorem degreeZeroN7TowerQuartic810_eq_pureA_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticLTowerFace810 l A +
        n7QuarticBetaTowerFace810 beta A +
        n7QuarticDeltaTowerFace810 delta A +
        n7QuarticZetaTowerFace810 zeta A +
        n7QuarticThetaTowerFace810 theta A +
        n7QuarticNoPureA810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN7TowerQuartic810, degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810, degreeZeroOmicronQuartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n7QuarticNoPureA810, n7QuarticNoPureA1810, n7QuarticNoPureA2810, n7QuarticNoPureA3810, n7QuarticNoPureA4810, n7QuarticNoPureA5810, n7QuarticNoPureA6810, n7QuarticNoPureA7810, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-! ## Generic chunk bounds -/

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA1810` containing 5 monomials. -/
def n7QuarticNoPureA1810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 2048 : k)) • (A ^ 2 * B ^ 3 * C)
  + (23 / 8192 : k) • (A * B ^ 5)
  - (5 / 512 : k) • (A * B ^ 3 * E)
  + (15 / 512 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA1810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA1810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 2048) : k), (23 / 8192 : k), (-(5 / 512) : k),
      (15 / 512 : k), (-(125 / 2048) : k)
      ]
      [
      [2, 3, 1, 0, 0, 0, 0], [1, 5, 0, 0, 0, 0, 0], [1, 3, 0, 0, 1, 0, 0], [1, 1, 3, 0, 0, 0, 0],
      [0, 4, 0, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA1810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA1810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 5 * B.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 4 * B.natDegree + D.natDegree < d) :
    (n7QuarticNoPureA1810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA1810` containing 5 monomials. -/
def n7QuarticNoPureA1810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((265 / 2048 : k) • (B ^ 3 * C ^ 2))
  - (5 / 64 : k) • (A * B * C * G)
  - (5 / 64 : k) • (A * C ^ 2 * F)
  - (5 / 64 : k) • (A * C * D * E)
  + (15 / 256 : k) • (B ^ 3 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA1810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA1810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(265 / 2048) : k), (-(5 / 64) : k), (-(5 / 64) : k),
      (-(5 / 64) : k), (15 / 256 : k)
      ]
      [
      [0, 3, 2, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 1], [1, 0, 2, 0, 0, 1, 0], [1, 0, 1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0, 0, 1]
      ] := by
  simp only [n7QuarticNoPureA1810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA1810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : 3 * B.natDegree + G.natDegree < d) :
    (n7QuarticNoPureA1810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA1810` containing 5 monomials. -/
def n7QuarticNoPureA1810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA1810_chunk3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA1810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (85 / 256 : k), (85 / 256 : k), (45 / 128 : k),
      (45 / 128 : k), (15 / 128 : k)
      ]
      [
      [0, 2, 1, 0, 0, 1, 0], [0, 2, 0, 1, 1, 0, 0], [0, 1, 2, 0, 1, 0, 0], [0, 1, 1, 2, 0, 0, 0],
      [0, 0, 3, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA1810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA1810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd11 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd14 : 3 * C.natDegree + D.natDegree < d) :
    (n7QuarticNoPureA1810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA1810` containing 5 monomials. -/
def n7QuarticNoPureA1810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 : k) • (B * E * G))
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA1810_chunk4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA1810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (-(5 / 16) : k), (-(5 / 16) : k),
      (-(5 / 8) : k), (-(5 / 16) : k)
      ]
      [
      [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 0, 2, 0], [0, 0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0],
      [0, 0, 0, 2, 0, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA1810_chunk4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA1810_chunk4_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd15 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd16 : B.natDegree + 2 * F.natDegree < d)
    (hd17 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd18 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd19 : 2 * D.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA1810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA1810_chunk4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA1810` by additive regrouping. -/
theorem n7QuarticNoPureA1810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA1810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA1810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA1810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA1810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA1810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA1810, n7QuarticNoPureA1810_chunk1, n7QuarticNoPureA1810_chunk2, n7QuarticNoPureA1810_chunk3, n7QuarticNoPureA1810_chunk4, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA1810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 3 * B.natDegree + C.natDegree < d)
    (hd1 : A.natDegree + 5 * B.natDegree < d)
    (hd2 : A.natDegree + 3 * B.natDegree + E.natDegree < d)
    (hd3 : A.natDegree + B.natDegree + 3 * C.natDegree < d)
    (hd4 : 4 * B.natDegree + D.natDegree < d)
    (hd5 : 3 * B.natDegree + 2 * C.natDegree < d)
    (hd6 : A.natDegree + B.natDegree + C.natDegree + G.natDegree < d)
    (hd7 : A.natDegree + 2 * C.natDegree + F.natDegree < d)
    (hd8 : A.natDegree + C.natDegree + D.natDegree + E.natDegree < d)
    (hd9 : 3 * B.natDegree + G.natDegree < d)
    (hd10 : 2 * B.natDegree + C.natDegree + F.natDegree < d)
    (hd11 : 2 * B.natDegree + D.natDegree + E.natDegree < d)
    (hd12 : B.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd13 : B.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd14 : 3 * C.natDegree + D.natDegree < d)
    (hd15 : B.natDegree + E.natDegree + G.natDegree < d)
    (hd16 : B.natDegree + 2 * F.natDegree < d)
    (hd17 : C.natDegree + D.natDegree + G.natDegree < d)
    (hd18 : C.natDegree + E.natDegree + F.natDegree < d)
    (hd19 : 2 * D.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA1810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA1810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA1810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA1810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10 hd11 hd12 hd13 hd14)) (n7QuarticNoPureA1810_chunk4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd15 hd16 hd17 hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA2810` containing 5 monomials. -/
def n7QuarticNoPureA2810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (D * E ^ 2)
  + (315 / 524288 * l : k) • (A ^ 6 * C)
  - (315 / 2097152 * l : k) • (A ^ 5 * B ^ 2)
  + (315 / 131072 * l : k) • (A ^ 5 * E)
  - (315 / 262144 * l : k) • (A ^ 4 * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA2810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA2810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16) : k), (315 / 524288 * l : k), (-(315 / 2097152 * l) : k),
      (315 / 131072 * l : k), (-(315 / 262144 * l) : k)
      ]
      [
      [0, 0, 0, 1, 2, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA2810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA2810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : D.natDegree + 2 * E.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d) :
    (n7QuarticNoPureA2810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA2810` containing 5 monomials. -/
def n7QuarticNoPureA2810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1485 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (63 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  - (45 / 524288 * l : k) • (A ^ 2 * B ^ 4)
  + (315 / 32768 * l : k) • (A ^ 4 * G)
  - (45 / 8192 * l : k) • (A ^ 3 * B * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA2810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA2810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1485 / 524288 * l : k), (-(63 / 131072 * l) : k), (-(45 / 524288 * l) : k),
      (315 / 32768 * l : k), (-(45 / 8192 * l) : k)
      ]
      [
      [4, 0, 2, 0, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 0, 1],
      [3, 1, 0, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA2810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA2810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd8 : 4 * A.natDegree + G.natDegree < d)
    (hd9 : 3 * A.natDegree + B.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA2810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA2810` containing 5 monomials. -/
def n7QuarticNoPureA2810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (171 / 8192 * l : k) • (A ^ 3 * C * E)
  - (45 / 16384 * l : k) • (A ^ 3 * D ^ 2)
  - (45 / 16384 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C * D)
  - (9 / 8192 * l : k) • (A ^ 2 * C ^ 3)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA2810_chunk3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA2810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (171 / 8192 * l : k), (-(45 / 16384 * l) : k), (-(45 / 16384 * l) : k),
      (9 / 4096 * l : k), (-(9 / 8192 * l) : k)
      ]
      [
      [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0], [2, 2, 0, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0],
      [2, 0, 3, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA2810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA2810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 3 * C.natDegree < d) :
    (n7QuarticNoPureA2810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA2810` containing 5 monomials. -/
def n7QuarticNoPureA2810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((27 / 4096 * l : k) • (A * B ^ 3 * D))
  + (45 / 4096 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (9 / 128 * l : k) • (A ^ 2 * C * G)
  - (27 / 1024 * l : k) • (A ^ 2 * D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA2810_chunk4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA2810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(27 / 4096 * l) : k), (45 / 4096 * l : k), (-(567 / 16384 * l) : k),
      (9 / 128 * l : k), (-(27 / 1024 * l) : k)
      ]
      [
      [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1],
      [2, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA2810_chunk4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA2810_chunk4_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd16 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : 4 * B.natDegree + C.natDegree < d)
    (hd18 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd19 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA2810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA2810_chunk4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA2810` by additive regrouping. -/
theorem n7QuarticNoPureA2810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA2810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA2810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA2810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA2810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA2810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA2810, n7QuarticNoPureA2810_chunk1, n7QuarticNoPureA2810_chunk2, n7QuarticNoPureA2810_chunk3, n7QuarticNoPureA2810_chunk4, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA2810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : D.natDegree + 2 * E.natDegree < d)
    (hd1 : 6 * A.natDegree + C.natDegree < d)
    (hd2 : 5 * A.natDegree + 2 * B.natDegree < d)
    (hd3 : 5 * A.natDegree + E.natDegree < d)
    (hd4 : 4 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd5 : 4 * A.natDegree + 2 * C.natDegree < d)
    (hd6 : 3 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd7 : 2 * A.natDegree + 4 * B.natDegree < d)
    (hd8 : 4 * A.natDegree + G.natDegree < d)
    (hd9 : 3 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd10 : 3 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * D.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 3 * C.natDegree < d)
    (hd15 : A.natDegree + 3 * B.natDegree + D.natDegree < d)
    (hd16 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree < d)
    (hd17 : 4 * B.natDegree + C.natDegree < d)
    (hd18 : 2 * A.natDegree + C.natDegree + G.natDegree < d)
    (hd19 : 2 * A.natDegree + D.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA2810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA2810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA2810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA2810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10 hd11 hd12 hd13 hd14)) (n7QuarticNoPureA2810_chunk4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd15 hd16 hd17 hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA3810` containing 5 monomials. -/
def n7QuarticNoPureA3810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (81 / 2048 * l : k) • (A ^ 2 * E ^ 2)
  - (9 / 512 * l : k) • (A * B ^ 2 * G)
  - (9 / 256 * l : k) • (A * B * C * F)
  - (9 / 256 * l : k) • (A * C ^ 2 * E)
  - (9 / 512 * l : k) • (A * C * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA3810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA3810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (81 / 2048 * l : k), (-(9 / 512 * l) : k), (-(9 / 256 * l) : k),
      (-(9 / 256 * l) : k), (-(9 / 512 * l) : k)
      ]
      [
      [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 0, 2, 0, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA3810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA3810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d) :
    (n7QuarticNoPureA3810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA3810` containing 5 monomials. -/
def n7QuarticNoPureA3810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA3810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA3810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (27 / 512 * l : k), (45 / 256 * l : k), (45 / 512 * l : k),
      (189 / 1024 * l : k), (63 / 4096 * l : k)
      ]
      [
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [0, 0, 4, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA3810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA3810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d) :
    (n7QuarticNoPureA3810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA3810` containing 5 monomials. -/
def n7QuarticNoPureA3810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 32 * l : k) • (A * E * G)
  - (9 / 128 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA3810_chunk3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA3810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 32 * l : k), (-(9 / 128 * l) : k), (-(9 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(9 / 128 * l) : k)
      ]
      [
      [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0],
      [0, 0, 2, 0, 0, 0, 1]
      ] := by
  simp only [n7QuarticNoPureA3810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA3810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d) :
    (n7QuarticNoPureA3810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA3810` containing 5 monomials. -/
def n7QuarticNoPureA3810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 32 * l : k) • (C * D * F))
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (35 / 16384 * beta : k) • (A ^ 5 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA3810_chunk4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA3810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 32 * l) : k), (-(9 / 64 * l) : k), (-(9 / 64 * l) : k),
      (9 / 16 * l : k), (35 / 16384 * beta : k)
      ]
      [
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2],
      [5, 0, 1, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA3810_chunk4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA3810_chunk4_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d)
    (hd19 : 5 * A.natDegree + C.natDegree < d) :
    (n7QuarticNoPureA3810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA3810_chunk4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA3810` by additive regrouping. -/
theorem n7QuarticNoPureA3810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA3810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA3810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA3810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA3810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA3810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA3810, n7QuarticNoPureA3810_chunk1, n7QuarticNoPureA3810_chunk2, n7QuarticNoPureA3810_chunk3, n7QuarticNoPureA3810_chunk4, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA3810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * A.natDegree + 2 * E.natDegree < d)
    (hd1 : A.natDegree + 2 * B.natDegree + G.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree < d)
    (hd3 : A.natDegree + 2 * C.natDegree + E.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + 2 * D.natDegree < d)
    (hd5 : 3 * B.natDegree + F.natDegree < d)
    (hd6 : 2 * B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : 2 * B.natDegree + 2 * D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree + D.natDegree < d)
    (hd9 : 4 * C.natDegree < d)
    (hd10 : A.natDegree + E.natDegree + G.natDegree < d)
    (hd11 : A.natDegree + 2 * F.natDegree < d)
    (hd12 : B.natDegree + D.natDegree + G.natDegree < d)
    (hd13 : B.natDegree + E.natDegree + F.natDegree < d)
    (hd14 : 2 * C.natDegree + G.natDegree < d)
    (hd15 : C.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : C.natDegree + 2 * E.natDegree < d)
    (hd17 : 2 * D.natDegree + E.natDegree < d)
    (hd18 : 2 * G.natDegree < d)
    (hd19 : 5 * A.natDegree + C.natDegree < d) :
    (n7QuarticNoPureA3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA3810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA3810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA3810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA3810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10 hd11 hd12 hd13 hd14)) (n7QuarticNoPureA3810_chunk4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd15 hd16 hd17 hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA4810` containing 5 monomials. -/
def n7QuarticNoPureA4810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(35 / 65536 * beta : k)) • (A ^ 4 * B ^ 2)
  + (35 / 4096 * beta : k) • (A ^ 4 * E)
  - (35 / 8192 * beta : k) • (A ^ 3 * B * D)
  + (91 / 16384 * beta : k) • (A ^ 3 * C ^ 2)
  - (35 / 16384 * beta : k) • (A ^ 2 * B ^ 2 * C)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA4810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA4810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(35 / 65536 * beta) : k), (35 / 4096 * beta : k), (-(35 / 8192 * beta) : k),
      (91 / 16384 * beta : k), (-(35 / 16384 * beta) : k)
      ]
      [
      [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0], [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0],
      [2, 2, 1, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA4810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA4810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd1 : 4 * A.natDegree + E.natDegree < d)
    (hd2 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d) :
    (n7QuarticNoPureA4810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA4810` containing 5 monomials. -/
def n7QuarticNoPureA4810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (49 / 32768 * beta : k) • (A * B ^ 4)
  + (35 / 1024 * beta : k) • (A ^ 3 * G)
  - (21 / 1024 * beta : k) • (A ^ 2 * B * F)
  + (35 / 1024 * beta : k) • (A ^ 2 * C * E)
  - (21 / 2048 * beta : k) • (A ^ 2 * D ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA4810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA4810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (49 / 32768 * beta : k), (35 / 1024 * beta : k), (-(21 / 1024 * beta) : k),
      (35 / 1024 * beta : k), (-(21 / 2048 * beta) : k)
      ]
      [
      [1, 4, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 1], [2, 1, 0, 0, 0, 1, 0], [2, 0, 1, 0, 1, 0, 0],
      [2, 0, 0, 2, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA4810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA4810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : 3 * A.natDegree + G.natDegree < d)
    (hd7 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * A.natDegree + 2 * D.natDegree < d) :
    (n7QuarticNoPureA4810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA4810` containing 5 monomials. -/
def n7QuarticNoPureA4810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((7 / 1024 * beta : k) • (A * B ^ 2 * E))
  + (7 / 256 * beta : k) • (A * B * C * D)
  + (7 / 512 * beta : k) • (A * C ^ 3)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA4810_chunk3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA4810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 1024 * beta) : k), (7 / 256 * beta : k), (7 / 512 * beta : k),
      (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k)
      ]
      [
      [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0], [1, 0, 3, 0, 0, 0, 0], [0, 3, 0, 1, 0, 0, 0],
      [0, 2, 2, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA4810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA4810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 3 * C.natDegree < d)
    (hd13 : 3 * B.natDegree + D.natDegree < d)
    (hd14 : 2 * B.natDegree + 2 * C.natDegree < d) :
    (n7QuarticNoPureA4810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA4810` containing 5 monomials. -/
def n7QuarticNoPureA4810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((7 / 64 * beta : k) • (A * D * F))
  + (7 / 128 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA4810_chunk4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA4810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 64 * beta) : k), (7 / 128 * beta : k), (7 / 32 * beta : k),
      (7 / 32 * beta : k), (7 / 64 * beta : k)
      ]
      [
      [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 0, 2, 0, 0], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0],
      [0, 0, 2, 0, 1, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA4810_chunk4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA4810_chunk4_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : A.natDegree + 2 * E.natDegree < d)
    (hd17 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd18 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd19 : 2 * C.natDegree + E.natDegree < d) :
    (n7QuarticNoPureA4810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA4810_chunk4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA4810` by additive regrouping. -/
theorem n7QuarticNoPureA4810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA4810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA4810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA4810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA4810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA4810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA4810, n7QuarticNoPureA4810_chunk1, n7QuarticNoPureA4810_chunk2, n7QuarticNoPureA4810_chunk3, n7QuarticNoPureA4810_chunk4, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA4810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 4 * A.natDegree + 2 * B.natDegree < d)
    (hd1 : 4 * A.natDegree + E.natDegree < d)
    (hd2 : 3 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd3 : 3 * A.natDegree + 2 * C.natDegree < d)
    (hd4 : 2 * A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd5 : A.natDegree + 4 * B.natDegree < d)
    (hd6 : 3 * A.natDegree + G.natDegree < d)
    (hd7 : 2 * A.natDegree + B.natDegree + F.natDegree < d)
    (hd8 : 2 * A.natDegree + C.natDegree + E.natDegree < d)
    (hd9 : 2 * A.natDegree + 2 * D.natDegree < d)
    (hd10 : A.natDegree + 2 * B.natDegree + E.natDegree < d)
    (hd11 : A.natDegree + B.natDegree + C.natDegree + D.natDegree < d)
    (hd12 : A.natDegree + 3 * C.natDegree < d)
    (hd13 : 3 * B.natDegree + D.natDegree < d)
    (hd14 : 2 * B.natDegree + 2 * C.natDegree < d)
    (hd15 : A.natDegree + D.natDegree + F.natDegree < d)
    (hd16 : A.natDegree + 2 * E.natDegree < d)
    (hd17 : B.natDegree + C.natDegree + F.natDegree < d)
    (hd18 : B.natDegree + D.natDegree + E.natDegree < d)
    (hd19 : 2 * C.natDegree + E.natDegree < d) :
    (n7QuarticNoPureA4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA4810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA4810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA4810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA4810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10 hd11 hd12 hd13 hd14)) (n7QuarticNoPureA4810_chunk4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd15 hd16 hd17 hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA5810` containing 5 monomials. -/
def n7QuarticNoPureA5810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 64 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 16 * gamma : k) • (A * C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA5810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA5810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (7 / 64 * beta : k), (-(7 / 16 * beta) : k), (3 / 64 * gamma : k),
      (-(27 / 256 * gamma) : k), (-(3 / 16 * gamma) : k)
      ]
      [
      [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA5810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA5810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA5810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA5810` containing 5 monomials. -/
def n7QuarticNoPureA5810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA5810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA5810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (9 / 64 * gamma : k), (3 / 8 * gamma : k), (3 / 16 * gamma : k),
      (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k)
      ]
      [
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA5810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA5810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * B.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : B.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * C.natDegree + D.natDegree < d)
    (hd9 : E.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA5810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA5810` containing 5 monomials. -/
def n7QuarticNoPureA5810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 2048 * delta : k) • (A ^ 4 * C)
  - (15 / 8192 * delta : k) • (A ^ 3 * B ^ 2)
  + (15 / 512 * delta : k) • (A ^ 3 * E)
  - (15 / 1024 * delta : k) • (A ^ 2 * B * D)
  + (5 / 2048 * delta : k) • (A ^ 2 * C ^ 2)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA5810_chunk3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA5810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 2048 * delta : k), (-(15 / 8192 * delta) : k), (15 / 512 * delta : k),
      (-(15 / 1024 * delta) : k), (5 / 2048 * delta : k)
      ]
      [
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA5810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA5810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : 4 * A.natDegree + C.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd12 : 3 * A.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 2 * C.natDegree < d) :
    (n7QuarticNoPureA5810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA5810` containing 5 monomials. -/
def n7QuarticNoPureA5810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (25 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (15 / 128 * delta : k) • (A ^ 2 * G)
  - (5 / 64 * delta : k) • (A * B * F)
  - (5 / 64 * delta : k) • (A * C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA5810_chunk4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA5810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (25 / 1024 * delta : k), (-(135 / 4096 * delta) : k), (15 / 128 * delta : k),
      (-(5 / 64 * delta) : k), (-(5 / 64 * delta) : k)
      ]
      [
      [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1, 0],
      [1, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA5810_chunk4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA5810_chunk4_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd16 : 4 * B.natDegree < d)
    (hd17 : 2 * A.natDegree + G.natDegree < d)
    (hd18 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd19 : A.natDegree + C.natDegree + E.natDegree < d) :
    (n7QuarticNoPureA5810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA5810_chunk4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA5810` by additive regrouping. -/
theorem n7QuarticNoPureA5810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA5810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA5810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA5810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA5810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA5810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA5810, n7QuarticNoPureA5810_chunk1, n7QuarticNoPureA5810_chunk2, n7QuarticNoPureA5810_chunk3, n7QuarticNoPureA5810_chunk4, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA5810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : C.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * F.natDegree < d)
    (hd2 : A.natDegree + B.natDegree + 2 * C.natDegree < d)
    (hd3 : 3 * B.natDegree + C.natDegree < d)
    (hd4 : A.natDegree + C.natDegree + F.natDegree < d)
    (hd5 : 2 * B.natDegree + F.natDegree < d)
    (hd6 : B.natDegree + C.natDegree + E.natDegree < d)
    (hd7 : B.natDegree + 2 * D.natDegree < d)
    (hd8 : 2 * C.natDegree + D.natDegree < d)
    (hd9 : E.natDegree + F.natDegree < d)
    (hd10 : 4 * A.natDegree + C.natDegree < d)
    (hd11 : 3 * A.natDegree + 2 * B.natDegree < d)
    (hd12 : 3 * A.natDegree + E.natDegree < d)
    (hd13 : 2 * A.natDegree + B.natDegree + D.natDegree < d)
    (hd14 : 2 * A.natDegree + 2 * C.natDegree < d)
    (hd15 : A.natDegree + 2 * B.natDegree + C.natDegree < d)
    (hd16 : 4 * B.natDegree < d)
    (hd17 : 2 * A.natDegree + G.natDegree < d)
    (hd18 : A.natDegree + B.natDegree + F.natDegree < d)
    (hd19 : A.natDegree + C.natDegree + E.natDegree < d) :
    (n7QuarticNoPureA5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA5810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA5810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA5810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA5810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10 hd11 hd12 hd13 hd14)) (n7QuarticNoPureA5810_chunk4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd15 hd16 hd17 hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA6810` containing 5 monomials. -/
def n7QuarticNoPureA6810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 128 * delta : k)) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA6810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA6810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 128 * delta) : k), (25 / 128 * delta : k), (15 / 32 * delta : k),
      (5 / 64 * delta : k), (-(5 / 8 * delta) : k)
      ]
      [
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA6810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA6810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * C.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA6810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA6810` containing 5 monomials. -/
def n7QuarticNoPureA6810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((5 / 16 * delta : k) • E ^ 2)
  - (1 / 8 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA6810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA6810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(5 / 16 * delta) : k), (-(1 / 8 * epsilon) : k), (7 / 32 * epsilon : k),
      (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k)
      ]
      [
      [0, 0, 0, 0, 2, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0]
      ] := by
  simp only [n7QuarticNoPureA6810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA6810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * E.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd7 : 2 * B.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree < d)
    (hd9 : C.natDegree + F.natDegree < d) :
    (n7QuarticNoPureA6810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA6810` containing 5 monomials. -/
def n7QuarticNoPureA6810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((1 / 2 * epsilon : k) • (D * E))
  + (3 / 128 * zeta : k) • (A ^ 3 * C)
  - (3 / 512 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 32 * zeta : k) • (A ^ 2 * E)
  - (3 / 64 * zeta : k) • (A * B * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA6810_chunk3` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA6810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(1 / 2 * epsilon) : k), (3 / 128 * zeta : k), (-(3 / 512 * zeta) : k),
      (3 / 32 * zeta : k), (-(3 / 64 * zeta) : k)
      ]
      [
      [0, 0, 0, 1, 1, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA6810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA6810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : D.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + C.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd13 : 2 * A.natDegree + E.natDegree < d)
    (hd14 : A.natDegree + B.natDegree + D.natDegree < d) :
    (n7QuarticNoPureA6810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA6810` containing 5 monomials. -/
def n7QuarticNoPureA6810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  -((9 / 128 * zeta : k) • (A * C ^ 2))
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  + (3 / 8 * zeta : k) • (A * G)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA6810_chunk4` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk4
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA6810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(9 / 128 * zeta) : k), (27 / 128 * zeta : k), (3 / 8 * zeta : k),
      (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k)
      ]
      [
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA6810_chunk4, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA6810_chunk4_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd15 : A.natDegree + 2 * C.natDegree < d)
    (hd16 : 2 * B.natDegree + C.natDegree < d)
    (hd17 : A.natDegree + G.natDegree < d)
    (hd18 : B.natDegree + F.natDegree < d)
    (hd19 : C.natDegree + E.natDegree < d) :
    (n7QuarticNoPureA6810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA6810_chunk4]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA6810` by additive regrouping. -/
theorem n7QuarticNoPureA6810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA6810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA6810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA6810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA6810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA6810_chunk4 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA6810, n7QuarticNoPureA6810_chunk1, n7QuarticNoPureA6810_chunk2, n7QuarticNoPureA6810_chunk3, n7QuarticNoPureA6810_chunk4, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA6810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : A.natDegree + 2 * D.natDegree < d)
    (hd1 : 2 * B.natDegree + E.natDegree < d)
    (hd2 : B.natDegree + C.natDegree + D.natDegree < d)
    (hd3 : 3 * C.natDegree < d)
    (hd4 : D.natDegree + F.natDegree < d)
    (hd5 : 2 * E.natDegree < d)
    (hd6 : A.natDegree + C.natDegree + D.natDegree < d)
    (hd7 : 2 * B.natDegree + D.natDegree < d)
    (hd8 : B.natDegree + 2 * C.natDegree < d)
    (hd9 : C.natDegree + F.natDegree < d)
    (hd10 : D.natDegree + E.natDegree < d)
    (hd11 : 3 * A.natDegree + C.natDegree < d)
    (hd12 : 2 * A.natDegree + 2 * B.natDegree < d)
    (hd13 : 2 * A.natDegree + E.natDegree < d)
    (hd14 : A.natDegree + B.natDegree + D.natDegree < d)
    (hd15 : A.natDegree + 2 * C.natDegree < d)
    (hd16 : 2 * B.natDegree + C.natDegree < d)
    (hd17 : A.natDegree + G.natDegree < d)
    (hd18 : B.natDegree + F.natDegree < d)
    (hd19 : C.natDegree + E.natDegree < d) :
    (n7QuarticNoPureA6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA6810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA6810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA6810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA6810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10 hd11 hd12 hd13 hd14)) (n7QuarticNoPureA6810_chunk4_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd15 hd16 hd17 hd18 hd19))

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA7810` containing 5 monomials. -/
def n7QuarticNoPureA7810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * zeta : k)) • D ^ 2
  - (1 / 16 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA7810_chunk1` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA7810_chunk1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA7810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * zeta) : k), (-(1 / 16 * eta) : k), (3 / 64 * eta : k),
      (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k)
      ]
      [
      [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA7810_chunk1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA7810_chunk1_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d) :
    (n7QuarticNoPureA7810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA7810_chunk1]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA7810` containing 5 monomials. -/
def n7QuarticNoPureA7810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 / 16 * theta : k) • (A ^ 2 * C)
  - (1 / 64 * theta : k) • (A * B ^ 2)
  + (1 / 4 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA7810_chunk2` (5 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA7810_chunk2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA7810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 / 16 * theta : k), (-(1 / 64 * theta) : k), (1 / 4 * theta : k),
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k)
      ]
      [
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0]
      ] := by
  simp only [n7QuarticNoPureA7810_chunk2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA7810_chunk2_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd5 : 2 * A.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree < d)
    (hd7 : A.natDegree + E.natDegree < d)
    (hd8 : B.natDegree + D.natDegree < d)
    (hd9 : 2 * C.natDegree < d) :
    (n7QuarticNoPureA7810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA7810_chunk2]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- A subchunk of `n7QuarticNoPureA7810` containing 1 monomial. -/
def n7QuarticNoPureA7810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for `n7QuarticNoPureA7810_chunk3` (1 monomials).
The reflective degree checker of `Max11SpeedReflectDegLibScratch`
replaces `compute_degree` on every bound of this polynomial. -/
private theorem refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA7810_chunk3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA7810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1 * theta : k)
      ]
      [
      [0, 0, 0, 0, 0, 0, 1]
      ] := by
  simp only [n7QuarticNoPureA7810_chunk3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  all_goals module


set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA7810_chunk3_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd10 : G.natDegree < d) :
    (n7QuarticNoPureA7810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [refl810PolyOf_ChamberN7Ladder_n7QuarticNoPureA7810_chunk3]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The small subchunks recover `n7QuarticNoPureA7810` by additive regrouping. -/
theorem n7QuarticNoPureA7810_split_chunks
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    n7QuarticNoPureA7810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticNoPureA7810_chunk1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA7810_chunk2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
        n7QuarticNoPureA7810_chunk3 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [n7QuarticNoPureA7810, n7QuarticNoPureA7810_chunk1, n7QuarticNoPureA7810_chunk2, n7QuarticNoPureA7810_chunk3, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 64000000 in
theorem n7QuarticNoPureA7810_natDegree_lt
    {d : ℕ}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hd0 : 2 * D.natDegree < d)
    (hd1 : A.natDegree + B.natDegree + C.natDegree < d)
    (hd2 : 3 * B.natDegree < d)
    (hd3 : B.natDegree + E.natDegree < d)
    (hd4 : C.natDegree + D.natDegree < d)
    (hd5 : 2 * A.natDegree + C.natDegree < d)
    (hd6 : A.natDegree + 2 * B.natDegree < d)
    (hd7 : A.natDegree + E.natDegree < d)
    (hd8 : B.natDegree + D.natDegree < d)
    (hd9 : 2 * C.natDegree < d)
    (hd10 : G.natDegree < d) :
    (n7QuarticNoPureA7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < d := by
  rw [n7QuarticNoPureA7810_split_chunks]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n7QuarticNoPureA7810_chunk1_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd0 hd1 hd2 hd3 hd4) (n7QuarticNoPureA7810_chunk2_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd5 hd6 hd7 hd8 hd9)) (n7QuarticNoPureA7810_chunk3_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G hd10))

set_option maxHeartbeats 64000000 in
/-- Everything of `N₇` below its pure-`A` `l` column, once the
lighter pure-`A` loads are zero. -/
def n7QuarticCostRestL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticBetaTowerFace810 beta A +
    n7QuarticDeltaTowerFace810 delta A +
    n7QuarticZetaTowerFace810 zeta A +
    n7QuarticThetaTowerFace810 theta A +
    n7QuarticNoPureA810 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7TowerQuartic810_eq_lColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7TowerQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticLTowerFace810 l A +
        n7QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN7TowerQuartic810_eq_pureA_add_rest]
  simp only [n7QuarticCostRestL810, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add]
  ring

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₇` is its unique top. -/
def QuarticN7CostTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree ∧
    B.natDegree + E.natDegree + G.natDegree < 8 * A.natDegree ∧
    B.natDegree + 2 * F.natDegree < 8 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 7 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree ∧
    C.natDegree + D.natDegree + G.natDegree < 8 * A.natDegree ∧
    C.natDegree + E.natDegree + F.natDegree < 8 * A.natDegree ∧
    2 * D.natDegree + F.natDegree < 8 * A.natDegree ∧
    D.natDegree + 2 * E.natDegree < 8 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 6 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 7 * A.natDegree ∧
    3 * B.natDegree + G.natDegree < 8 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + F.natDegree < 8 * A.natDegree ∧
    2 * B.natDegree + D.natDegree + E.natDegree < 8 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 7 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree + E.natDegree < 8 * A.natDegree ∧
    B.natDegree + C.natDegree + 2 * D.natDegree < 8 * A.natDegree ∧
    3 * C.natDegree + D.natDegree < 8 * A.natDegree ∧
    5 * B.natDegree < 7 * A.natDegree ∧
    4 * B.natDegree + D.natDegree < 8 * A.natDegree

set_option maxHeartbeats 64000000 in
theorem n7QuarticCostRestL810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + C.natDegree + G.natDegree < 7 * A.natDegree)
    (hp1 : B.natDegree + E.natDegree + G.natDegree < 8 * A.natDegree)
    (hp2 : B.natDegree + 2 * F.natDegree < 8 * A.natDegree)
    (hp3 : 2 * C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp4 : C.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp5 : C.natDegree + D.natDegree + G.natDegree < 8 * A.natDegree)
    (hp6 : C.natDegree + E.natDegree + F.natDegree < 8 * A.natDegree)
    (hp7 : 2 * D.natDegree + F.natDegree < 8 * A.natDegree)
    (hp8 : D.natDegree + 2 * E.natDegree < 8 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 7 * A.natDegree)
    (hp11 : 3 * B.natDegree + G.natDegree < 8 * A.natDegree)
    (hp12 : 2 * B.natDegree + C.natDegree + F.natDegree < 8 * A.natDegree)
    (hp13 : 2 * B.natDegree + D.natDegree + E.natDegree < 8 * A.natDegree)
    (hp14 : B.natDegree + 3 * C.natDegree < 7 * A.natDegree)
    (hp15 : B.natDegree + 2 * C.natDegree + E.natDegree < 8 * A.natDegree)
    (hp16 : B.natDegree + C.natDegree + 2 * D.natDegree < 8 * A.natDegree)
    (hp17 : 3 * C.natDegree + D.natDegree < 8 * A.natDegree)
    (hp18 : 5 * B.natDegree < 7 * A.natDegree)
    (hp19 : 4 * B.natDegree + D.natDegree < 8 * A.natDegree) :
    (n7QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      8 * A.natDegree := by
  simp only [n7QuarticCostRestL810]
  have hfbeta : (n7QuarticBetaTowerFace810 beta A).natDegree <
      8 * A.natDegree := by
    simp only [n7QuarticBetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hfdelta : (n7QuarticDeltaTowerFace810 delta A).natDegree <
      8 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hfzeta : (n7QuarticZetaTowerFace810 zeta A).natDegree <
      8 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hftheta : (n7QuarticThetaTowerFace810 theta A).natDegree <
      8 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hnp : (n7QuarticNoPureA810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      8 * A.natDegree := by
    have hn1 : (n7QuarticNoPureA1810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA1810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn2 : (n7QuarticNoPureA2810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA2810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn3 : (n7QuarticNoPureA3810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA3810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn4 : (n7QuarticNoPureA4810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA4810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn5 : (n7QuarticNoPureA5810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA5810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn6 : (n7QuarticNoPureA6810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA6810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn7 : (n7QuarticNoPureA7810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 8 * A.natDegree := by
      apply n7QuarticNoPureA7810_natDegree_lt l beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    simp only [n7QuarticNoPureA810]
    exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hn1 hn2) hn3) hn4) hn5) hn6) hn7)
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hfbeta hfdelta) hfzeta) hftheta) hnp

set_option maxHeartbeats 64000000 in
/-- Everything of `N₇` below its pure-`A` `beta` column, once the
lighter pure-`A` loads are zero. -/
def n7QuarticCostRestBeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticDeltaTowerFace810 delta A +
    n7QuarticZetaTowerFace810 zeta A +
    n7QuarticThetaTowerFace810 theta A +
    n7QuarticNoPureA810 0 beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7TowerQuartic810_eq_betaColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7TowerQuartic810 0 beta gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticBetaTowerFace810 beta A +
        n7QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN7TowerQuartic810_eq_pureA_add_rest]
  simp only [n7QuarticCostRestBeta810, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add]
  ring

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₇` is its unique top. -/
def QuarticN7CostTopBeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree ∧
    B.natDegree + E.natDegree + G.natDegree < 7 * A.natDegree ∧
    B.natDegree + 2 * F.natDegree < 7 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 6 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree ∧
    C.natDegree + D.natDegree + G.natDegree < 7 * A.natDegree ∧
    C.natDegree + E.natDegree + F.natDegree < 7 * A.natDegree ∧
    2 * D.natDegree + F.natDegree < 7 * A.natDegree ∧
    D.natDegree + 2 * E.natDegree < 7 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 6 * A.natDegree ∧
    3 * B.natDegree + G.natDegree < 7 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + F.natDegree < 7 * A.natDegree ∧
    2 * B.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree + E.natDegree < 7 * A.natDegree ∧
    B.natDegree + C.natDegree + 2 * D.natDegree < 7 * A.natDegree ∧
    3 * C.natDegree + D.natDegree < 7 * A.natDegree ∧
    5 * B.natDegree < 6 * A.natDegree ∧
    4 * B.natDegree + D.natDegree < 7 * A.natDegree

set_option maxHeartbeats 64000000 in
theorem n7QuarticCostRestBeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + C.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : B.natDegree + E.natDegree + G.natDegree < 7 * A.natDegree)
    (hp2 : B.natDegree + 2 * F.natDegree < 7 * A.natDegree)
    (hp3 : 2 * C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp4 : C.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp5 : C.natDegree + D.natDegree + G.natDegree < 7 * A.natDegree)
    (hp6 : C.natDegree + E.natDegree + F.natDegree < 7 * A.natDegree)
    (hp7 : 2 * D.natDegree + F.natDegree < 7 * A.natDegree)
    (hp8 : D.natDegree + 2 * E.natDegree < 7 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 6 * A.natDegree)
    (hp11 : 3 * B.natDegree + G.natDegree < 7 * A.natDegree)
    (hp12 : 2 * B.natDegree + C.natDegree + F.natDegree < 7 * A.natDegree)
    (hp13 : 2 * B.natDegree + D.natDegree + E.natDegree < 7 * A.natDegree)
    (hp14 : B.natDegree + 3 * C.natDegree < 6 * A.natDegree)
    (hp15 : B.natDegree + 2 * C.natDegree + E.natDegree < 7 * A.natDegree)
    (hp16 : B.natDegree + C.natDegree + 2 * D.natDegree < 7 * A.natDegree)
    (hp17 : 3 * C.natDegree + D.natDegree < 7 * A.natDegree)
    (hp18 : 5 * B.natDegree < 6 * A.natDegree)
    (hp19 : 4 * B.natDegree + D.natDegree < 7 * A.natDegree) :
    (n7QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
  simp only [n7QuarticCostRestBeta810]
  have hfdelta : (n7QuarticDeltaTowerFace810 delta A).natDegree <
      7 * A.natDegree := by
    simp only [n7QuarticDeltaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hfzeta : (n7QuarticZetaTowerFace810 zeta A).natDegree <
      7 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hftheta : (n7QuarticThetaTowerFace810 theta A).natDegree <
      7 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hnp : (n7QuarticNoPureA810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      7 * A.natDegree := by
    have hn1 : (n7QuarticNoPureA1810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      apply n7QuarticNoPureA1810_natDegree_lt 0 beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn2 : (n7QuarticNoPureA2810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      rw [n7QuarticNoPureA2810_split_chunks]
      have hc1 : (n7QuarticNoPureA2810_chunk1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA2810_chunk2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc3 : (n7QuarticNoPureA2810_chunk3 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA2810_chunk4 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn3 : (n7QuarticNoPureA3810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      rw [n7QuarticNoPureA3810_split_chunks]
      have hc1 : (n7QuarticNoPureA3810_chunk1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA3810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc2 : (n7QuarticNoPureA3810_chunk2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA3810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc3 : (n7QuarticNoPureA3810_chunk3 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA3810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA3810_chunk4 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
        simp only [n7QuarticNoPureA3810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn4 : (n7QuarticNoPureA4810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      apply n7QuarticNoPureA4810_natDegree_lt 0 beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn5 : (n7QuarticNoPureA5810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      apply n7QuarticNoPureA5810_natDegree_lt 0 beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn6 : (n7QuarticNoPureA6810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      apply n7QuarticNoPureA6810_natDegree_lt 0 beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn7 : (n7QuarticNoPureA7810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 7 * A.natDegree := by
      apply n7QuarticNoPureA7810_natDegree_lt 0 beta gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    simp only [n7QuarticNoPureA810]
    exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hn1 hn2) hn3) hn4) hn5) hn6) hn7)
  exact natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hfdelta hfzeta) hftheta) hnp

set_option maxHeartbeats 64000000 in
/-- Everything of `N₇` below its pure-`A` `delta` column, once the
lighter pure-`A` loads are zero. -/
def n7QuarticCostRestDelta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticZetaTowerFace810 zeta A +
    n7QuarticThetaTowerFace810 theta A +
    n7QuarticNoPureA810 0 0 gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7TowerQuartic810_eq_deltaColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7TowerQuartic810 0 0 gamma delta epsilon zeta eta theta A B C D E F G =
      n7QuarticDeltaTowerFace810 delta A +
        n7QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN7TowerQuartic810_eq_pureA_add_rest]
  simp only [n7QuarticCostRestDelta810, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add]
  ring

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₇` is its unique top. -/
def QuarticN7CostTopDelta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree ∧
    B.natDegree + E.natDegree + G.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * F.natDegree < 6 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 5 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree ∧
    C.natDegree + D.natDegree + G.natDegree < 6 * A.natDegree ∧
    C.natDegree + E.natDegree + F.natDegree < 6 * A.natDegree ∧
    2 * D.natDegree + F.natDegree < 6 * A.natDegree ∧
    D.natDegree + 2 * E.natDegree < 6 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + G.natDegree < 6 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + F.natDegree < 6 * A.natDegree ∧
    2 * B.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree + E.natDegree < 6 * A.natDegree ∧
    B.natDegree + C.natDegree + 2 * D.natDegree < 6 * A.natDegree ∧
    3 * C.natDegree + D.natDegree < 6 * A.natDegree ∧
    B.natDegree < A.natDegree ∧
    4 * B.natDegree + D.natDegree < 6 * A.natDegree ∧
    C.natDegree + F.natDegree < 5 * A.natDegree ∧
    E.natDegree + F.natDegree < 6 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 5 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 6 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 6 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 6 * A.natDegree

set_option maxHeartbeats 64000000 in
theorem n7QuarticCostRestDelta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + C.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : B.natDegree + E.natDegree + G.natDegree < 6 * A.natDegree)
    (hp2 : B.natDegree + 2 * F.natDegree < 6 * A.natDegree)
    (hp3 : 2 * C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp4 : C.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp5 : C.natDegree + D.natDegree + G.natDegree < 6 * A.natDegree)
    (hp6 : C.natDegree + E.natDegree + F.natDegree < 6 * A.natDegree)
    (hp7 : 2 * D.natDegree + F.natDegree < 6 * A.natDegree)
    (hp8 : D.natDegree + 2 * E.natDegree < 6 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 5 * A.natDegree)
    (hp11 : 3 * B.natDegree + G.natDegree < 6 * A.natDegree)
    (hp12 : 2 * B.natDegree + C.natDegree + F.natDegree < 6 * A.natDegree)
    (hp13 : 2 * B.natDegree + D.natDegree + E.natDegree < 6 * A.natDegree)
    (hp14 : B.natDegree + 3 * C.natDegree < 5 * A.natDegree)
    (hp15 : B.natDegree + 2 * C.natDegree + E.natDegree < 6 * A.natDegree)
    (hp16 : B.natDegree + C.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp17 : 3 * C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp18 : B.natDegree < A.natDegree)
    (hp19 : 4 * B.natDegree + D.natDegree < 6 * A.natDegree)
    (hp20 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp21 : E.natDegree + F.natDegree < 6 * A.natDegree)
    (hp22 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp23 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree)
    (hp24 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree)
    (hp25 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp26 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp27 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree) :
    (n7QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  simp only [n7QuarticCostRestDelta810]
  have hfzeta : (n7QuarticZetaTowerFace810 zeta A).natDegree <
      6 * A.natDegree := by
    simp only [n7QuarticZetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hftheta : (n7QuarticThetaTowerFace810 theta A).natDegree <
      6 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hnp : (n7QuarticNoPureA810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
    have hn1 : (n7QuarticNoPureA1810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      apply n7QuarticNoPureA1810_natDegree_lt 0 0 gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn2 : (n7QuarticNoPureA2810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      rw [n7QuarticNoPureA2810_split_chunks]
      have hc1 : (n7QuarticNoPureA2810_chunk1 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA2810_chunk2 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc3 : (n7QuarticNoPureA2810_chunk3 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA2810_chunk4 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn3 : (n7QuarticNoPureA3810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      simp only [n7QuarticNoPureA3810, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
      omega
    have hn4 : (n7QuarticNoPureA4810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      simp only [n7QuarticNoPureA4810, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
      omega
    have hn5 : (n7QuarticNoPureA5810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      rw [n7QuarticNoPureA5810_split_chunks]
      have hc1 : (n7QuarticNoPureA5810_chunk1 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA5810_chunk2 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        apply n7QuarticNoPureA5810_chunk2_natDegree_lt 0 0 gamma delta epsilon zeta eta theta A B C D E F G <;> omega
      have hc3 : (n7QuarticNoPureA5810_chunk3 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        apply n7QuarticNoPureA5810_chunk3_natDegree_lt 0 0 gamma delta epsilon zeta eta theta A B C D E F G <;> omega
      have hc4 : (n7QuarticNoPureA5810_chunk4 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
        apply n7QuarticNoPureA5810_chunk4_natDegree_lt 0 0 gamma delta epsilon zeta eta theta A B C D E F G <;> omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn6 : (n7QuarticNoPureA6810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      apply n7QuarticNoPureA6810_natDegree_lt 0 0 gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    have hn7 : (n7QuarticNoPureA7810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree < 6 * A.natDegree := by
      apply n7QuarticNoPureA7810_natDegree_lt 0 0 gamma delta epsilon zeta eta theta A B C D E F G <;> omega
    simp only [n7QuarticNoPureA810]
    exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hn1 hn2) hn3) hn4) hn5) hn6) hn7)
  exact natDegree_add_lt810 (natDegree_add_lt810 hfzeta hftheta) hnp

set_option maxHeartbeats 64000000 in
/-- Everything of `N₇` below its pure-`A` `zeta` column, once the
lighter pure-`A` loads are zero. -/
def n7QuarticCostRestZeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticThetaTowerFace810 theta A +
    n7QuarticNoPureA810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7TowerQuartic810_eq_zetaColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7TowerQuartic810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G =
      n7QuarticZetaTowerFace810 zeta A +
        n7QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G := by
  rw [degreeZeroN7TowerQuartic810_eq_pureA_add_rest]
  simp only [n7QuarticCostRestZeta810, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add]
  ring

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₇` is its unique top. -/
def QuarticN7CostTopZeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree ∧
    B.natDegree + E.natDegree + G.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * F.natDegree < 5 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree + G.natDegree < 5 * A.natDegree ∧
    C.natDegree + E.natDegree + F.natDegree < 5 * A.natDegree ∧
    2 * D.natDegree + F.natDegree < 5 * A.natDegree ∧
    D.natDegree + 2 * E.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 3 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + G.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + F.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree + E.natDegree < 5 * A.natDegree ∧
    B.natDegree + C.natDegree + 2 * D.natDegree < 5 * A.natDegree ∧
    3 * C.natDegree + D.natDegree < 5 * A.natDegree ∧
    5 * B.natDegree < 4 * A.natDegree ∧
    4 * B.natDegree + D.natDegree < 5 * A.natDegree ∧
    C.natDegree + F.natDegree < 4 * A.natDegree ∧
    E.natDegree + F.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 4 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 5 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 5 * A.natDegree ∧
    C.natDegree + D.natDegree < 4 * A.natDegree ∧
    C.natDegree + F.natDegree < 5 * A.natDegree ∧
    D.natDegree + E.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 5 * A.natDegree

set_option maxHeartbeats 64000000 in
theorem n7QuarticCostRestZeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + C.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : B.natDegree + E.natDegree + G.natDegree < 5 * A.natDegree)
    (hp2 : B.natDegree + 2 * F.natDegree < 5 * A.natDegree)
    (hp3 : 2 * C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp4 : C.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp5 : C.natDegree + D.natDegree + G.natDegree < 5 * A.natDegree)
    (hp6 : C.natDegree + E.natDegree + F.natDegree < 5 * A.natDegree)
    (hp7 : 2 * D.natDegree + F.natDegree < 5 * A.natDegree)
    (hp8 : D.natDegree + 2 * E.natDegree < 5 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp11 : 3 * B.natDegree + G.natDegree < 5 * A.natDegree)
    (hp12 : 2 * B.natDegree + C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp13 : 2 * B.natDegree + D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp14 : B.natDegree + 3 * C.natDegree < 4 * A.natDegree)
    (hp15 : B.natDegree + 2 * C.natDegree + E.natDegree < 5 * A.natDegree)
    (hp16 : B.natDegree + C.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp17 : 3 * C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp18 : 5 * B.natDegree < 4 * A.natDegree)
    (hp19 : 4 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp20 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp21 : E.natDegree + F.natDegree < 5 * A.natDegree)
    (hp22 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp23 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp24 : B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree)
    (hp25 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp26 : 2 * C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp27 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree)
    (hp28 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp29 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp30 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp31 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp32 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (n7QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  simp only [n7QuarticCostRestZeta810]
  have hftheta : (n7QuarticThetaTowerFace810 theta A).natDegree <
      5 * A.natDegree := by
    simp only [n7QuarticThetaTowerFace810]
    refine natDegree_smul_lt810 _ ?_
    rw [natDegree_pow]
    omega
  have hnp : (n7QuarticNoPureA810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
    have hn1 : (n7QuarticNoPureA1810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      apply n7QuarticNoPureA1810_natDegree_lt 0 0 gamma 0 epsilon zeta eta theta A B C D E F G <;> omega
    have hn2 : (n7QuarticNoPureA2810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      rw [n7QuarticNoPureA2810_split_chunks]
      have hc1 : (n7QuarticNoPureA2810_chunk1 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA2810_chunk2 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc3 : (n7QuarticNoPureA2810_chunk3 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA2810_chunk4 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn3 : (n7QuarticNoPureA3810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      simp only [n7QuarticNoPureA3810, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
      omega
    have hn4 : (n7QuarticNoPureA4810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      simp only [n7QuarticNoPureA4810, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
      omega
    have hn5 : (n7QuarticNoPureA5810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      rw [n7QuarticNoPureA5810_split_chunks]
      have hc1 : (n7QuarticNoPureA5810_chunk1 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA5810_chunk2 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        apply n7QuarticNoPureA5810_chunk2_natDegree_lt 0 0 gamma 0 epsilon zeta eta theta A B C D E F G <;> omega
      have hc3 : (n7QuarticNoPureA5810_chunk3 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA5810_chunk4 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn6 : (n7QuarticNoPureA6810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      rw [n7QuarticNoPureA6810_split_chunks]
      have hc1 : (n7QuarticNoPureA6810_chunk1 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA6810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc2 : (n7QuarticNoPureA6810_chunk2 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        simp only [n7QuarticNoPureA6810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc3 : (n7QuarticNoPureA6810_chunk3 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        apply n7QuarticNoPureA6810_chunk3_natDegree_lt 0 0 gamma 0 epsilon zeta eta theta A B C D E F G <;> omega
      have hc4 : (n7QuarticNoPureA6810_chunk4 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
        apply n7QuarticNoPureA6810_chunk4_natDegree_lt 0 0 gamma 0 epsilon zeta eta theta A B C D E F G <;> omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn7 : (n7QuarticNoPureA7810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree < 5 * A.natDegree := by
      apply n7QuarticNoPureA7810_natDegree_lt 0 0 gamma 0 epsilon zeta eta theta A B C D E F G <;> omega
    simp only [n7QuarticNoPureA810]
    exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hn1 hn2) hn3) hn4) hn5) hn6) hn7)
  exact natDegree_add_lt810 hftheta hnp

set_option maxHeartbeats 64000000 in
/-- Everything of `N₇` below its pure-`A` `theta` column, once the
lighter pure-`A` loads are zero. -/
def n7QuarticCostRestTheta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n7QuarticNoPureA810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
theorem degreeZeroN7TowerQuartic810_eq_thetaColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN7TowerQuartic810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G =
      n7QuarticThetaTowerFace810 theta A +
        n7QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G := by
  rw [degreeZeroN7TowerQuartic810_eq_pureA_add_rest]
  simp only [n7QuarticCostRestTheta810, n7QuarticLTowerFace810, n7QuarticBetaTowerFace810, n7QuarticDeltaTowerFace810, n7QuarticZetaTowerFace810, n7QuarticThetaTowerFace810, zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add]

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `theta` column of `N₇` is its unique top. -/
def QuarticN7CostTopTheta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree ∧
    B.natDegree + E.natDegree + G.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * F.natDegree < 4 * A.natDegree ∧
    2 * C.natDegree + F.natDegree < 3 * A.natDegree ∧
    C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree ∧
    C.natDegree + D.natDegree + G.natDegree < 4 * A.natDegree ∧
    C.natDegree + E.natDegree + F.natDegree < 4 * A.natDegree ∧
    2 * D.natDegree + F.natDegree < 4 * A.natDegree ∧
    D.natDegree + 2 * E.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 2 * A.natDegree ∧
    3 * B.natDegree + E.natDegree < 3 * A.natDegree ∧
    3 * B.natDegree + G.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree ∧
    B.natDegree + 3 * C.natDegree < 3 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree + E.natDegree < 4 * A.natDegree ∧
    B.natDegree + C.natDegree + 2 * D.natDegree < 4 * A.natDegree ∧
    3 * C.natDegree + D.natDegree < 4 * A.natDegree ∧
    5 * B.natDegree < 3 * A.natDegree ∧
    4 * B.natDegree + D.natDegree < 4 * A.natDegree ∧
    C.natDegree + F.natDegree < 3 * A.natDegree ∧
    E.natDegree + F.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 3 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 4 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree < 3 * A.natDegree ∧
    C.natDegree + F.natDegree < 4 * A.natDegree ∧
    D.natDegree + E.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 4 * A.natDegree ∧
    B.natDegree + C.natDegree < 3 * A.natDegree ∧
    B.natDegree + E.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree < 4 * A.natDegree

set_option maxHeartbeats 64000000 in
theorem n7QuarticCostRestTheta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + C.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : B.natDegree + E.natDegree + G.natDegree < 4 * A.natDegree)
    (hp2 : B.natDegree + 2 * F.natDegree < 4 * A.natDegree)
    (hp3 : 2 * C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp4 : C.natDegree + D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp5 : C.natDegree + D.natDegree + G.natDegree < 4 * A.natDegree)
    (hp6 : C.natDegree + E.natDegree + F.natDegree < 4 * A.natDegree)
    (hp7 : 2 * D.natDegree + F.natDegree < 4 * A.natDegree)
    (hp8 : D.natDegree + 2 * E.natDegree < 4 * A.natDegree)
    (hp9 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp11 : 3 * B.natDegree + G.natDegree < 4 * A.natDegree)
    (hp12 : 2 * B.natDegree + C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp13 : 2 * B.natDegree + D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp14 : B.natDegree + 3 * C.natDegree < 3 * A.natDegree)
    (hp15 : B.natDegree + 2 * C.natDegree + E.natDegree < 4 * A.natDegree)
    (hp16 : B.natDegree + C.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp17 : 3 * C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp18 : 5 * B.natDegree < 3 * A.natDegree)
    (hp19 : 4 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp20 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp21 : E.natDegree + F.natDegree < 4 * A.natDegree)
    (hp22 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp23 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp24 : B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree)
    (hp25 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp26 : 2 * C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp27 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp28 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp29 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp30 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp31 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp32 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree)
    (hp33 : B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp34 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp35 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp36 : 3 * B.natDegree < 4 * A.natDegree) :
    (n7QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  simp only [n7QuarticCostRestTheta810]
  have hnp : (n7QuarticNoPureA810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
    have hn1 : (n7QuarticNoPureA1810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      apply n7QuarticNoPureA1810_natDegree_lt 0 0 gamma 0 epsilon 0 eta theta A B C D E F G <;> omega
    have hn2 : (n7QuarticNoPureA2810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      rw [n7QuarticNoPureA2810_split_chunks]
      have hc1 : (n7QuarticNoPureA2810_chunk1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA2810_chunk2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc3 : (n7QuarticNoPureA2810_chunk3 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA2810_chunk4 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA2810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn3 : (n7QuarticNoPureA3810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      simp only [n7QuarticNoPureA3810, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
      omega
    have hn4 : (n7QuarticNoPureA4810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      simp only [n7QuarticNoPureA4810, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
      omega
    have hn5 : (n7QuarticNoPureA5810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      rw [n7QuarticNoPureA5810_split_chunks]
      have hc1 : (n7QuarticNoPureA5810_chunk1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA5810_chunk2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        apply n7QuarticNoPureA5810_chunk2_natDegree_lt 0 0 gamma 0 epsilon 0 eta theta A B C D E F G <;> omega
      have hc3 : (n7QuarticNoPureA5810_chunk3 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc4 : (n7QuarticNoPureA5810_chunk4 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA5810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn6 : (n7QuarticNoPureA6810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      rw [n7QuarticNoPureA6810_split_chunks]
      have hc1 : (n7QuarticNoPureA6810_chunk1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA6810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      have hc2 : (n7QuarticNoPureA6810_chunk2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA6810_chunk2, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc3 : (n7QuarticNoPureA6810_chunk3 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA6810_chunk3, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc4 : (n7QuarticNoPureA6810_chunk4 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA6810_chunk4, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub, natDegree_zero]
        omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3) hc4)
    have hn7 : (n7QuarticNoPureA7810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
      rw [n7QuarticNoPureA7810_split_chunks]
      have hc1 : (n7QuarticNoPureA7810_chunk1 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        simp only [n7QuarticNoPureA7810_chunk1, mul_zero, zero_mul, zero_smul, smul_zero, neg_zero, zero_add, add_zero, sub_zero, zero_sub]
        compute_degree <;> omega
      have hc2 : (n7QuarticNoPureA7810_chunk2 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        apply n7QuarticNoPureA7810_chunk2_natDegree_lt 0 0 gamma 0 epsilon 0 eta theta A B C D E F G <;> omega
      have hc3 : (n7QuarticNoPureA7810_chunk3 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree < 4 * A.natDegree := by
        apply n7QuarticNoPureA7810_chunk3_natDegree_lt 0 0 gamma 0 epsilon 0 eta theta A B C D E F G <;> omega
      exact (natDegree_add_lt810 (natDegree_add_lt810 hc1 hc2) hc3)
    simp only [n7QuarticNoPureA810]
    exact (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 (natDegree_add_lt810 hn1 hn2) hn3) hn4) hn5) hn6) hn7)
  exact hnp

/-! ## The `N₇` kills, bands and cascade -/

set_option maxHeartbeats 64000000 in
theorem quarticN7CostTopBeta810_imp_L810
    {A B C D E F G : k[X]}
    (h : QuarticN7CostTopBeta810 A B C D E F G) :
    QuarticN7CostTopL810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
theorem quarticN7CostTopDelta810_imp_Beta810
    {A B C D E F G : k[X]}
    (h : QuarticN7CostTopDelta810 A B C D E F G) :
    QuarticN7CostTopBeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
theorem quarticN7CostTopZeta810_imp_Delta810
    {A B C D E F G : k[X]}
    (h : QuarticN7CostTopZeta810 A B C D E F G) :
    QuarticN7CostTopDelta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30, hp31, hp32⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
theorem quarticN7CostTopTheta810_imp_Zeta810
    {A B C D E F G : k[X]}
    (h : QuarticN7CostTopTheta810 A B C D E F G) :
    QuarticN7CostTopZeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30, hp31, hp32, hp33, hp34, hp35, hp36⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `l` in cost form, via the tower lane's
`quarticSigma_l_eq_zero_of_N7_column`. -/
theorem quarticSigmaN7Cost_l_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN7CostTopL810 A B C D E F G)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    l = 0 := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19⟩ := id htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hrest := n7QuarticCostRestL810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19
  have hle := degreeZeroN7TowerQuartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos hprim homi hnu hkap
  exact quarticSigma_l_eq_zero_of_N7_column l beta gamma delta epsilon zeta eta theta
    A B C D E F G (n7QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G) hApos
    hrest hle (degreeZeroN7TowerQuartic810_eq_lColumn_add_rest l beta gamma delta epsilon zeta eta theta
      A B C D E F G)

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `beta` in cost form, via the tower lane's
`quarticSigma_beta_eq_zero_of_N7_column`. -/
theorem quarticSigmaN7Cost_beta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN7CostTopBeta810 A B C D E F G)
    (hl0 : l = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    beta = 0 := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19⟩ := id htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hrest := n7QuarticCostRestBeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19
  subst hl0
  have hle := degreeZeroN7TowerQuartic810_natDegree_le 0 beta gamma delta epsilon zeta eta theta
    A B C D E F G hApos hprim homi hnu hkap
  exact quarticSigma_beta_eq_zero_of_N7_column 0 beta gamma delta epsilon zeta eta theta
    A B C D E F G (n7QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G) hApos rfl
    hrest hle (degreeZeroN7TowerQuartic810_eq_betaColumn_add_rest 0 beta gamma delta epsilon zeta eta theta
      A B C D E F G)

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `delta` in cost form, via the tower lane's
`quarticSigma_delta_eq_zero_of_N7_column`. -/
theorem quarticSigmaN7Cost_delta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN7CostTopDelta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    delta = 0 := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27⟩ := id htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hrest := n7QuarticCostRestDelta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23 hp24 hp25 hp26 hp27
  subst hl0
  subst hbeta0
  have hle := degreeZeroN7TowerQuartic810_natDegree_le 0 0 gamma delta epsilon zeta eta theta
    A B C D E F G hApos hprim homi hnu hkap
  exact quarticSigma_delta_eq_zero_of_N7_column 0 0 gamma delta epsilon zeta eta theta
    A B C D E F G (n7QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G) hApos rfl rfl
    hrest hle (degreeZeroN7TowerQuartic810_eq_deltaColumn_add_rest 0 0 gamma delta epsilon zeta eta theta
      A B C D E F G)

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `zeta` in cost form, via the tower lane's
`quarticSigma_zeta_eq_zero_of_N7_column`. -/
theorem quarticSigmaN7Cost_zeta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN7CostTopZeta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    zeta = 0 := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30, hp31, hp32⟩ := id htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hrest := n7QuarticCostRestZeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23 hp24 hp25 hp26 hp27 hp28 hp29 hp30 hp31 hp32
  subst hl0
  subst hbeta0
  subst hdelta0
  have hle := degreeZeroN7TowerQuartic810_natDegree_le 0 0 gamma 0 epsilon zeta eta theta
    A B C D E F G hApos hprim homi hnu hkap
  exact quarticSigma_zeta_eq_zero_of_N7_column 0 0 gamma 0 epsilon zeta eta theta
    A B C D E F G (n7QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G) hApos rfl rfl rfl
    hrest hle (degreeZeroN7TowerQuartic810_eq_zetaColumn_add_rest 0 0 gamma 0 epsilon zeta eta theta
      A B C D E F G)

set_option maxHeartbeats 64000000 in
/-- `N₇` kills `theta` in cost form, via the tower lane's
`quarticSigma_theta_eq_zero_of_N7_column`. -/
theorem quarticSigmaN7Cost_theta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN7CostTopTheta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    theta = 0 := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30, hp31, hp32, hp33, hp34, hp35, hp36⟩ := id htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hrest := n7QuarticCostRestTheta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22 hp23 hp24 hp25 hp26 hp27 hp28 hp29 hp30 hp31 hp32 hp33 hp34 hp35 hp36
  subst hl0
  subst hbeta0
  subst hdelta0
  subst hzeta0
  have hle := degreeZeroN7TowerQuartic810_natDegree_le 0 0 gamma 0 epsilon 0 eta theta
    A B C D E F G hApos hprim homi hnu hkap
  exact quarticSigma_theta_eq_zero_of_N7_column 0 0 gamma 0 epsilon 0 eta theta
    A B C D E F G (n7QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G) hApos rfl rfl rfl rfl
    hrest hle (degreeZeroN7TowerQuartic810_eq_thetaColumn_add_rest 0 0 gamma 0 epsilon 0 eta theta
      A B C D E F G)


/-! Axiom audit of the final load-kill theorems. -/

#print axioms quarticSigmaN7Cost_l_eq_zero
#print axioms quarticSigmaN7Cost_beta_eq_zero
#print axioms quarticSigmaN7Cost_delta_eq_zero
#print axioms quarticSigmaN7Cost_zeta_eq_zero
#print axioms quarticSigmaN7Cost_theta_eq_zero

end QuarticN7Ladder810

end Max11DegreeRoutes
