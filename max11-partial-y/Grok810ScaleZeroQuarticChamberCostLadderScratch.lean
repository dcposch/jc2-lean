import Grok810ScaleZeroQuarticChamberResidualScratch
import Grok810ScaleZeroQuarticLoadLadderScratch
import Max11SpeedReflectDegLibScratch

/-! # The cost-form `κ`/`N₂` load ladder, `(8,10)` scale zero

`QuarticKappaLoadTop<P>810` of File A asks `2·s_X > w·a` for *every*
letter, which implies but is not equivalent to `c₀(κ) > w·a`; the
chamber taxonomy's band-strictness flags were computed against the
latter, so File A's band is too weak on 525 (leaf, carrier) pairs.
This module states the kill in cost form — one inequality per *minimal*
load-free monomial of the auxiliary, plus one per minimal monomial of
each lighter load column that has no pure-`A` monomial — and proves the
same five kills for `κ` and for `N₂ = ν + (1/8)·A·κ`, whose pure-`A`
column sits one `A` higher and therefore reaches loads `κ` cannot
(`~/lean/tools/sigma810/OPEN_CHAMBERS.md` §1).  Untracked working note.
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

section QuarticCostLadder810

/-! ## `κ` in cost form: `c₀(κ) > w_π·a` instead of `2·s_X > w_π·a` -/

set_option maxHeartbeats 64000000 in
/-- `κ` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 1/2): 20 monomials. -/
def kappaQuarticCostRestL810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (45 / 8192 * l : k) • (A ^ 3 * C)
  - (9 / 16384 * l : k) • (A ^ 2 * B ^ 2)
  + (27 / 1024 * l : k) • (A ^ 2 * E)
  - (9 / 512 * l : k) • (A * B * D)
  + (9 / 1024 * l : k) • (A * C ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * C)
  + (9 / 64 * l : k) • (A * G)
  + (9 / 64 * l : k) • (B * F)
  + (9 / 64 * l : k) • (C * E)
  + (9 / 128 * l : k) • D ^ 2
  + (35 / 32768 * beta : k) • A ^ 4
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)

set_option maxHeartbeats 64000000 in
/-- `κ` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 2/2): 14 monomials. -/
def kappaQuarticCostRestL810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(7 / 64 * beta : k)) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def kappaQuarticCostRestL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    kappaQuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `κ` splits
into its pure-`A` `l` column `c·l·A^5` and the rest. -/
theorem degreeZeroKappaQuartic810_eq_lCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticLFace810 l A +
        kappaQuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticLFace810, kappaQuarticCostRestL810, kappaQuarticCostRestL810c1, kappaQuarticCostRestL810c2,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_kappaQuarticCostRestL810c1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    kappaQuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 16 : k),
      (45 / 8192 * l : k), (-(9 / 16384 * l) : k), (27 / 1024 * l : k),
      (-(9 / 512 * l) : k), (9 / 1024 * l : k), (-(63 / 1024 * l) : k),
      (9 / 64 * l : k), (9 / 64 * l : k), (9 / 64 * l : k),
      (9 / 128 * l : k), (35 / 32768 * beta : k), (21 / 1024 * beta : k),
      (7 / 1024 * beta : k), (7 / 64 * beta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0]] := by
  simp only [kappaQuarticCostRestL810c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestL810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp3 : 3 * B.natDegree < 4 * A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (kappaQuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [astra810l_kappaQuarticCostRestL810c1_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_kappaQuarticCostRestL810c2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    kappaQuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k), (7 / 8 * beta : k),
      (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k), (5 / 1024 * delta : k),
      (5 / 64 * delta : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k),
      (1 / 2 * epsilon : k), (3 / 128 * zeta : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [kappaQuarticCostRestL810c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestL810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp3 : 3 * B.natDegree < 4 * A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (kappaQuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [astra810l_kappaQuarticCostRestL810c2_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestL810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 5 * A.natDegree)
    (hp3 : 3 * B.natDegree < 4 * A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree) :
    (kappaQuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  simp only [kappaQuarticCostRestL810]
  exact (natDegree_add_lt810 (kappaQuarticCostRestL810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5) (kappaQuarticCostRestL810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `κ` is its unique top: every
load-free monomial costs more than `1·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticKappaCostTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + G.natDegree < 5 * A.natDegree ∧
    C.natDegree + F.natDegree < 5 * A.natDegree ∧
    D.natDegree + E.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `κ` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 1/2): 20 monomials. -/
def kappaQuarticCostRestBeta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  + (21 / 1024 * beta : k) • (A ^ 2 * C)
  + (7 / 1024 * beta : k) • (A * B ^ 2)
  + (7 / 64 * beta : k) • (A * E)
  - (7 / 64 * beta : k) • (B * D)
  - (7 / 128 * beta : k) • C ^ 2
  + (7 / 8 * beta : k) • G
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 1024 * delta : k) • A ^ 3
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2

set_option maxHeartbeats 64000000 in
/-- `κ` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 2/2): 3 monomials. -/
def kappaQuarticCostRestBeta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
def kappaQuarticCostRestBeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  kappaQuarticCostRestBeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    kappaQuarticCostRestBeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `κ` splits
into its pure-`A` `beta` column `c·beta·A^4` and the rest. -/
theorem degreeZeroKappaQuartic810_eq_betaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticBetaFace810 beta A +
        kappaQuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticBetaFace810, kappaQuarticCostRestBeta810, kappaQuarticCostRestBeta810c1, kappaQuarticCostRestBeta810c2,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_kappaQuarticCostRestBeta810c1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    kappaQuarticCostRestBeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 16 : k),
      (21 / 1024 * beta : k), (7 / 1024 * beta : k), (7 / 64 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k), (7 / 8 * beta : k),
      (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k), (5 / 1024 * delta : k),
      (5 / 64 * delta : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k),
      (1 / 2 * epsilon : k), (3 / 128 * zeta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0]] := by
  simp only [kappaQuarticCostRestBeta810c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestBeta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree < A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree) :
    (kappaQuarticCostRestBeta810c1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [astra810l_kappaQuarticCostRestBeta810c1_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_kappaQuarticCostRestBeta810c2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    kappaQuarticCostRestBeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [kappaQuarticCostRestBeta810c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestBeta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree < A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree) :
    (kappaQuarticCostRestBeta810c2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [astra810l_kappaQuarticCostRestBeta810c2_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestBeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 4 * A.natDegree)
    (hp3 : B.natDegree < A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree) :
    (kappaQuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  simp only [kappaQuarticCostRestBeta810]
  exact (natDegree_add_lt810 (kappaQuarticCostRestBeta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5) (kappaQuarticCostRestBeta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `κ` is its unique top: every
load-free monomial costs more than `3·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticKappaCostTopBeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + G.natDegree < 4 * A.natDegree ∧
    C.natDegree + F.natDegree < 4 * A.natDegree ∧
    D.natDegree + E.natDegree < 4 * A.natDegree ∧
    B.natDegree < A.natDegree ∧
    2 * B.natDegree + D.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 4 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `κ` off its pure-`A` `delta` column, with the lighter
pure-`A` loads set to zero: 16 monomials. -/
def kappaQuarticCostRestDelta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (5 / 64 * delta : k) • (A * C)
  - (15 / 128 * delta : k) • B ^ 2
  + (5 / 8 * delta : k) • E
  + (1 / 2 * epsilon : k) • D
  + (3 / 128 * zeta : k) • A ^ 2
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `κ` splits
into its pure-`A` `delta` column `c·delta·A^3` and the rest. -/
theorem degreeZeroKappaQuartic810_eq_deltaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 0 gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticDeltaFace810 delta A +
        kappaQuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticDeltaFace810, kappaQuarticCostRestDelta810,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_kappaQuarticCostRestDelta810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    kappaQuarticCostRestDelta810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 16 : k),
      (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k), (5 / 64 * delta : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (1 / 2 * epsilon : k),
      (3 / 128 * zeta : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [kappaQuarticCostRestDelta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestDelta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 3 * A.natDegree)
    (hp3 : 3 * B.natDegree < 2 * A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree)
    (hp6 : F.natDegree < 3 * A.natDegree)
    (hp7 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (kappaQuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [astra810l_kappaQuarticCostRestDelta810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `κ` is its unique top: every
load-free monomial costs more than `5·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticKappaCostTopDelta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + G.natDegree < 3 * A.natDegree ∧
    C.natDegree + F.natDegree < 3 * A.natDegree ∧
    D.natDegree + E.natDegree < 3 * A.natDegree ∧
    3 * B.natDegree < 2 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 3 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 3 * A.natDegree ∧
    F.natDegree < 3 * A.natDegree ∧
    B.natDegree + C.natDegree < 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `κ` off its pure-`A` `zeta` column, with the lighter
pure-`A` loads set to zero: 12 monomials. -/
def kappaQuarticCostRestZeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (5 / 512 : k) • (A * B ^ 3)
  - (15 / 128 : k) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (1 / 2 * epsilon : k) • D
  + (3 / 8 * zeta : k) • C
  + (1 / 4 * eta : k) • B
  + (1 / 8 * theta : k) • A

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `κ` splits
into its pure-`A` `zeta` column `c·zeta·A^2` and the rest. -/
theorem degreeZeroKappaQuartic810_eq_zetaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G =
      kappaQuarticZetaFace810 zeta A +
        kappaQuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticZetaFace810, kappaQuarticCostRestZeta810,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  module

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_kappaQuarticCostRestZeta810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    kappaQuarticCostRestZeta810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (5 / 512 : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 16 : k),
      (-(3 / 16 * gamma) : k), (3 / 4 * gamma : k), (1 / 2 * epsilon : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 3, 0, 0, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]] := by
  simp only [kappaQuarticCostRestZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem kappaQuarticCostRestZeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : B.natDegree + G.natDegree < 2 * A.natDegree)
    (hp1 : C.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : D.natDegree + E.natDegree < 2 * A.natDegree)
    (hp3 : 3 * B.natDegree < A.natDegree)
    (hp4 : 2 * B.natDegree + D.natDegree < 2 * A.natDegree)
    (hp5 : B.natDegree + 2 * C.natDegree < 2 * A.natDegree)
    (hp6 : F.natDegree < 2 * A.natDegree)
    (hp7 : B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp8 : D.natDegree < 2 * A.natDegree) :
    (kappaQuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      2 * A.natDegree := by
  rw [astra810l_kappaQuarticCostRestZeta810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `κ` is its unique top: every
load-free monomial costs more than `7·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticKappaCostTopZeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    B.natDegree + G.natDegree < 2 * A.natDegree ∧
    C.natDegree + F.natDegree < 2 * A.natDegree ∧
    D.natDegree + E.natDegree < 2 * A.natDegree ∧
    3 * B.natDegree < A.natDegree ∧
    2 * B.natDegree + D.natDegree < 2 * A.natDegree ∧
    B.natDegree + 2 * C.natDegree < 2 * A.natDegree ∧
    F.natDegree < 2 * A.natDegree ∧
    B.natDegree + C.natDegree < 2 * A.natDegree ∧
    D.natDegree < 2 * A.natDegree

/-! ### `κ` cost-form monotonicity, kills and bands -/

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `κ` tops it only if the cheaper `l`
column does. -/
theorem quarticKappaCostTopBeta810_imp_L810
    {A B C D E F G : k[X]}
    (h : QuarticKappaCostTopBeta810 A B C D E F G) :
    QuarticKappaCostTopL810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `κ` tops it only if the cheaper `beta`
column does. -/
theorem quarticKappaCostTopDelta810_imp_Beta810
    {A B C D E F G : k[X]}
    (h : QuarticKappaCostTopDelta810 A B C D E F G) :
    QuarticKappaCostTopBeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `κ` tops it only if the cheaper `delta`
column does. -/
theorem quarticKappaCostTopZeta810_imp_Delta810
    {A B C D E F G : k[X]}
    (h : QuarticKappaCostTopZeta810 A B C D E F G) :
    QuarticKappaCostTopDelta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `l` column tops `κ` then
`l = 0`, because `natDegree κ ≤ 0·a < 5·a`. -/
theorem quarticSigmaKappaCost_l_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaCostTopL810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    l = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (63 / 262144 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticLFace810 l A).natDegree = 5 * A.natDegree := by
    simp only [kappaQuarticLFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := kappaQuarticCostRestL810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5
  rw [degreeZeroKappaQuartic810_eq_lCostColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `beta` column tops `κ` then
`beta = 0`, because `natDegree κ ≤ 0·a < 4·a`. -/
theorem quarticSigmaKappaCost_beta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaCostTopBeta810 A B C D E F G)
    (hl0 : l = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    beta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (35 / 32768 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticBetaFace810 beta A).natDegree = 4 * A.natDegree := by
    simp only [kappaQuarticBetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := kappaQuarticCostRestBeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5
  subst hl0
  rw [degreeZeroKappaQuartic810_eq_betaCostColumn_add_rest (l := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `delta` column tops `κ` then
`delta = 0`, because `natDegree κ ≤ 0·a < 3·a`. -/
theorem quarticSigmaKappaCost_delta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaCostTopDelta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    delta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (5 / 1024 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticDeltaFace810 delta A).natDegree = 3 * A.natDegree := by
    simp only [kappaQuarticDeltaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := kappaQuarticCostRestDelta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7
  subst hl0
  subst hbeta0
  rw [degreeZeroKappaQuartic810_eq_deltaCostColumn_add_rest (l := 0) (beta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `zeta` column tops `κ` then
`zeta = 0`, because `natDegree κ ≤ 0·a < 2·a`. -/
theorem quarticSigmaKappaCost_zeta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticKappaCostTopZeta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    zeta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (3 / 128 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (kappaQuarticZetaFace810 zeta A).natDegree = 2 * A.natDegree := by
    simp only [kappaQuarticZetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := kappaQuarticCostRestZeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8
  subst hl0
  subst hbeta0
  subst hdelta0
  rw [degreeZeroKappaQuartic810_eq_zetaCostColumn_add_rest (l := 0) (beta := 0) (delta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaKappaCost_l_band
    {l : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaCostTopL810 A B C D E F G → l = 0) :
    l = 0 ∨
      5 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree := by
  by_cases hb0 : B.natDegree + G.natDegree < 5 * A.natDegree
  · by_cases hb1 : C.natDegree + F.natDegree < 5 * A.natDegree
    · by_cases hb2 : D.natDegree + E.natDegree < 5 * A.natDegree
      · by_cases hb3 : 3 * B.natDegree < 4 * A.natDegree
        · by_cases hb4 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * C.natDegree < 5 * A.natDegree
            · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))
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
theorem quarticSigmaKappaCost_beta_band
    {beta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaCostTopBeta810 A B C D E F G → beta = 0) :
    beta = 0 ∨
      4 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree := by
  by_cases hb0 : B.natDegree + G.natDegree < 4 * A.natDegree
  · by_cases hb1 : C.natDegree + F.natDegree < 4 * A.natDegree
    · by_cases hb2 : D.natDegree + E.natDegree < 4 * A.natDegree
      · by_cases hb3 : B.natDegree < A.natDegree
        · by_cases hb4 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * C.natDegree < 4 * A.natDegree
            · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5⟩)
            · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))
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
theorem quarticSigmaKappaCost_delta_band
    {delta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaCostTopDelta810 A B C D E F G → delta = 0) :
    delta = 0 ∨
      3 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      3 * A.natDegree ≤ F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree := by
  by_cases hb0 : B.natDegree + G.natDegree < 3 * A.natDegree
  · by_cases hb1 : C.natDegree + F.natDegree < 3 * A.natDegree
    · by_cases hb2 : D.natDegree + E.natDegree < 3 * A.natDegree
      · by_cases hb3 : 3 * B.natDegree < 2 * A.natDegree
        · by_cases hb4 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * C.natDegree < 3 * A.natDegree
            · by_cases hb6 : F.natDegree < 3 * A.natDegree
              · by_cases hb7 : B.natDegree + C.natDegree < 3 * A.natDegree
                · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩)
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))
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
theorem quarticSigmaKappaCost_zeta_band
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticKappaCostTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      2 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      2 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      A.natDegree ≤ 3 * B.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      2 * A.natDegree ≤ F.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + C.natDegree ∨
      2 * A.natDegree ≤ D.natDegree := by
  by_cases hb0 : B.natDegree + G.natDegree < 2 * A.natDegree
  · by_cases hb1 : C.natDegree + F.natDegree < 2 * A.natDegree
    · by_cases hb2 : D.natDegree + E.natDegree < 2 * A.natDegree
      · by_cases hb3 : 3 * B.natDegree < A.natDegree
        · by_cases hb4 : 2 * B.natDegree + D.natDegree < 2 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * C.natDegree < 2 * A.natDegree
            · by_cases hb6 : F.natDegree < 2 * A.natDegree
              · by_cases hb7 : B.natDegree + C.natDegree < 2 * A.natDegree
                · by_cases hb8 : D.natDegree < 2 * A.natDegree
                  · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩)
                  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))
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
/-- The cost-form `κ` ladder as five band disjunctions. -/
theorem quarticSigmaKappaCostBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    (l = 0 ∨
      5 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * C.natDegree) ∧
    (beta = 0 ∨
      4 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * C.natDegree) ∧
    (delta = 0 ∨
      3 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      3 * A.natDegree ≤ F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree) ∧
    (zeta = 0 ∨
      2 * A.natDegree ≤ B.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ C.natDegree + F.natDegree ∨
      2 * A.natDegree ≤ D.natDegree + E.natDegree ∨
      A.natDegree ≤ 3 * B.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + 2 * C.natDegree ∨
      2 * A.natDegree ≤ F.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + C.natDegree ∨
      2 * A.natDegree ≤ D.natDegree) := by
  by_cases hTl : QuarticKappaCostTopL810 A B C D E F G
  · have hl0 : l = 0 :=
      quarticSigmaKappaCost_l_eq_zero l beta gamma delta epsilon zeta eta theta
        A B C D E F G hTl hkap
    by_cases hTbeta : QuarticKappaCostTopBeta810 A B C D E F G
    · have hbeta0 : beta = 0 :=
        quarticSigmaKappaCost_beta_eq_zero l beta gamma delta epsilon zeta eta theta
          A B C D E F G hTbeta hl0 hkap
      by_cases hTdelta : QuarticKappaCostTopDelta810 A B C D E F G
      · have hdelta0 : delta = 0 :=
          quarticSigmaKappaCost_delta_eq_zero l beta gamma delta epsilon zeta eta theta
            A B C D E F G hTdelta hl0 hbeta0 hkap
        by_cases hTzeta : QuarticKappaCostTopZeta810 A B C D E F G
        · have hzeta0 : zeta = 0 :=
            quarticSigmaKappaCost_zeta_eq_zero l beta gamma delta epsilon zeta eta theta
              A B C D E F G hTzeta hl0 hbeta0 hdelta0 hkap
          exact ⟨Or.inl hl0, Or.inl hbeta0, Or.inl hdelta0, Or.inl hzeta0⟩
        · exact ⟨Or.inl hl0,
            Or.inl hbeta0,
            Or.inl hdelta0,
            quarticSigmaKappaCost_zeta_band (zeta := zeta) A B C D E F G hA
              (fun htop => absurd (htop) hTzeta)⟩
      · exact ⟨Or.inl hl0,
          Or.inl hbeta0,
          quarticSigmaKappaCost_delta_band (delta := delta) A B C D E F G hA
            (fun htop => absurd (htop) hTdelta),
          quarticSigmaKappaCost_zeta_band (zeta := zeta) A B C D E F G hA
            (fun htop => absurd (quarticKappaCostTopZeta810_imp_Delta810 (htop)) hTdelta)⟩
    · exact ⟨Or.inl hl0,
        quarticSigmaKappaCost_beta_band (beta := beta) A B C D E F G hA
          (fun htop => absurd (htop) hTbeta),
        quarticSigmaKappaCost_delta_band (delta := delta) A B C D E F G hA
          (fun htop => absurd (quarticKappaCostTopDelta810_imp_Beta810 (htop)) hTbeta),
        quarticSigmaKappaCost_zeta_band (zeta := zeta) A B C D E F G hA
          (fun htop => absurd (quarticKappaCostTopDelta810_imp_Beta810 (quarticKappaCostTopZeta810_imp_Delta810 (htop))) hTbeta)⟩
  · exact ⟨quarticSigmaKappaCost_l_band (l := l) A B C D E F G hA
        (fun htop => absurd (htop) hTl),
      quarticSigmaKappaCost_beta_band (beta := beta) A B C D E F G hA
        (fun htop => absurd (quarticKappaCostTopBeta810_imp_L810 (htop)) hTl),
      quarticSigmaKappaCost_delta_band (delta := delta) A B C D E F G hA
        (fun htop => absurd (quarticKappaCostTopBeta810_imp_L810 (quarticKappaCostTopDelta810_imp_Beta810 (htop))) hTl),
      quarticSigmaKappaCost_zeta_band (zeta := zeta) A B C D E F G hA
        (fun htop => absurd (quarticKappaCostTopBeta810_imp_L810 (quarticKappaCostTopDelta810_imp_Beta810 (quarticKappaCostTopZeta810_imp_Delta810 (htop)))) hTl)⟩

/-! ## `N₂` in cost form: `c₀(N₂) > w_π·a` instead of `2·s_X > w_π·a` -/

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 1/3): 20 monomials. -/
def n2QuarticCostRestL810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (315 / 262144 * l : k) • (A ^ 4 * C)
  - (9 / 131072 * l : k) • (A ^ 3 * B ^ 2)
  + (45 / 8192 * l : k) • (A ^ 3 * E)
  - (9 / 8192 * l : k) • (A ^ 2 * B * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 2)
  + (63 / 8192 * l : k) • (A * B ^ 2 * C)
  + (315 / 32768 * l : k) • B ^ 4
  + (27 / 1024 * l : k) • (A ^ 2 * G)
  - (9 / 512 * l : k) • (A * B * F)
  + (9 / 512 * l : k) • (A * C * E)
  - (9 / 1024 * l : k) • (A * D ^ 2)
  - (63 / 1024 * l : k) • (B ^ 2 * E)

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 2/3): 20 monomials. -/
def n2QuarticCostRestL810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(63 / 512 * l : k)) • (B * C * D)
  - (21 / 1024 * l : k) • C ^ 3
  + (9 / 64 * l : k) • (C * G)
  + (9 / 64 * l : k) • (D * F)
  + (9 / 128 * l : k) • E ^ 2
  + (63 / 262144 * beta : k) • A ^ 5
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  + (35 / 32768 * delta : k) • A ^ 4

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `l` column, with the lighter
pure-`A` loads set to zero (chunk 3/3): 15 monomials. -/
def n2QuarticCostRestL810c3
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (5 / 1024 * zeta : k) • A ^ 3
  + (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  + (1 / 4 * eta : k) • D
  + (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def n2QuarticCostRestL810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n2QuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n2QuarticCostRestL810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₂` splits
into its pure-`A` `l` column `c·l·A^6` and the rest. -/
theorem degreeZeroN2Quartic810_eq_lCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticLFace810 l A +
        n2QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n2QuarticLFace810, n2QuarticCostRestL810, n2QuarticCostRestL810c1, n2QuarticCostRestL810c2, n2QuarticCostRestL810c3,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestL810c1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 512 : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (315 / 262144 * l : k),
      (-(9 / 131072 * l) : k), (45 / 8192 * l : k), (-(9 / 8192 * l) : k),
      (27 / 16384 * l : k), (63 / 8192 * l : k), (315 / 32768 * l : k),
      (27 / 1024 * l : k), (-(9 / 512 * l) : k), (9 / 512 * l : k),
      (-(9 / 1024 * l) : k), (-(63 / 1024 * l) : k)]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0],
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0]] := by
  simp only [n2QuarticCostRestL810c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestL810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree) :
    (n2QuarticCostRestL810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestL810c1_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestL810c2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(63 / 512 * l) : k), (-(21 / 1024 * l) : k), (9 / 64 * l : k),
      (9 / 64 * l : k), (9 / 128 * l : k), (63 / 262144 * beta : k),
      (35 / 8192 * beta : k), (7 / 16384 * beta : k), (21 / 1024 * beta : k),
      (7 / 512 * beta : k), (-(7 / 1024 * beta) : k), (63 / 1024 * beta : k),
      (7 / 64 * beta : k), (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k),
      (-(7 / 128 * beta) : k), (5 / 128 * gamma : k), (-(3 / 16 * gamma) : k),
      (-(3 / 16 * gamma) : k), (35 / 32768 * delta : k)]
      [
      [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestL810c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestL810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree) :
    (n2QuarticCostRestL810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestL810c2_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestL810c3_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestL810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 1024 * delta : k), (15 / 1024 * delta : k), (5 / 64 * delta : k),
      (-(15 / 64 * delta) : k), (-(15 / 128 * delta) : k), (5 / 8 * delta : k),
      (-(1 / 4 * epsilon) : k), (1 / 2 * epsilon : k), (5 / 1024 * zeta : k),
      (3 / 64 * zeta : k), (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (3 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0],
      [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestL810c3, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestL810c3_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree) :
    (n2QuarticCostRestL810c3 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestL810c3_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestL810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 6 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 6 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree) :
    (n2QuarticCostRestL810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      6 * A.natDegree := by
  simp only [n2QuarticCostRestL810]
  exact (natDegree_add_lt810 (natDegree_add_lt810 (n2QuarticCostRestL810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7) (n2QuarticCostRestL810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7)) (n2QuarticCostRestL810c3_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `l` column of `N₂` is its unique top: every
load-free monomial costs more than `1·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN2CostTopL810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D.natDegree + G.natDegree < 6 * A.natDegree ∧
    E.natDegree + F.natDegree < 6 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 6 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 6 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 6 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 6 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 1/2): 20 monomials. -/
def n2QuarticCostRestBeta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (35 / 8192 * beta : k) • (A ^ 3 * C)
  + (7 / 16384 * beta : k) • (A ^ 2 * B ^ 2)
  + (21 / 1024 * beta : k) • (A ^ 2 * E)
  + (7 / 512 * beta : k) • (A * B * D)
  - (7 / 1024 * beta : k) • (A * C ^ 2)
  + (63 / 1024 * beta : k) • (B ^ 2 * C)
  + (7 / 64 * beta : k) • (A * G)
  - (7 / 64 * beta : k) • (B * F)
  - (7 / 64 * beta : k) • (C * E)
  - (7 / 128 * beta : k) • D ^ 2
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `beta` column, with the lighter
pure-`A` loads set to zero (chunk 2/2): 17 monomials. -/
def n2QuarticCostRestBeta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (-(3 / 16 * gamma : k)) • (C * D)
  + (35 / 32768 * delta : k) • A ^ 4
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (5 / 1024 * zeta : k) • A ^ 3
  + (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  + (1 / 4 * eta : k) • D
  + (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def n2QuarticCostRestBeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticCostRestBeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n2QuarticCostRestBeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₂` splits
into its pure-`A` `beta` column `c·beta·A^5` and the rest. -/
theorem degreeZeroN2Quartic810_eq_betaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 0 beta gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticBetaFace810 beta A +
        n2QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n2QuarticBetaFace810, n2QuarticCostRestBeta810, n2QuarticCostRestBeta810c1, n2QuarticCostRestBeta810c2,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestBeta810c1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestBeta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 512 : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (35 / 8192 * beta : k),
      (7 / 16384 * beta : k), (21 / 1024 * beta : k), (7 / 512 * beta : k),
      (-(7 / 1024 * beta) : k), (63 / 1024 * beta : k), (7 / 64 * beta : k),
      (-(7 / 64 * beta) : k), (-(7 / 64 * beta) : k), (-(7 / 128 * beta) : k),
      (5 / 128 * gamma : k), (-(3 / 16 * gamma) : k)]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0],
      [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [1, 0, 2, 0, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0],
      [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0]] := by
  simp only [n2QuarticCostRestBeta810c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestBeta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree) :
    (n2QuarticCostRestBeta810c1 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestBeta810c1_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestBeta810c2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestBeta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(3 / 16 * gamma) : k), (35 / 32768 * delta : k), (15 / 1024 * delta : k),
      (15 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 64 * delta) : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (-(1 / 4 * epsilon) : k),
      (1 / 2 * epsilon : k), (5 / 1024 * zeta : k), (3 / 64 * zeta : k),
      (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k), (1 / 4 * eta : k),
      (3 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [0, 0, 1, 1, 0, 0, 0], [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0],
      [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestBeta810c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestBeta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree) :
    (n2QuarticCostRestBeta810c2 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestBeta810c2_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestBeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 5 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 5 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 5 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree) :
    (n2QuarticCostRestBeta810 0 beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      5 * A.natDegree := by
  simp only [n2QuarticCostRestBeta810]
  exact (natDegree_add_lt810 (n2QuarticCostRestBeta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7) (n2QuarticCostRestBeta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `beta` column of `N₂` is its unique top: every
load-free monomial costs more than `3·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN2CostTopBeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D.natDegree + G.natDegree < 5 * A.natDegree ∧
    E.natDegree + F.natDegree < 5 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 5 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 5 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 5 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 5 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `delta` column, with the lighter
pure-`A` loads set to zero (chunk 1/2): 20 monomials. -/
def n2QuarticCostRestDelta810c1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C)
  + (15 / 1024 * delta : k) • (A * B ^ 2)
  + (5 / 64 * delta : k) • (A * E)
  - (15 / 64 * delta : k) • (B * D)
  - (15 / 128 * delta : k) • C ^ 2
  + (5 / 8 * delta : k) • G
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (5 / 1024 * zeta : k) • A ^ 3

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `delta` column, with the lighter
pure-`A` loads set to zero (chunk 2/2): 6 monomials. -/
def n2QuarticCostRestDelta810c2
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  + (1 / 4 * eta : k) • D
  + (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
def n2QuarticCostRestDelta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  n2QuarticCostRestDelta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    n2QuarticCostRestDelta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₂` splits
into its pure-`A` `delta` column `c·delta·A^4` and the rest. -/
theorem degreeZeroN2Quartic810_eq_deltaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 0 0 gamma delta epsilon zeta eta theta A B C D E F G =
      n2QuarticDeltaFace810 delta A +
        n2QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n2QuarticDeltaFace810, n2QuarticCostRestDelta810, n2QuarticCostRestDelta810c1, n2QuarticCostRestDelta810c2,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestDelta810c1_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestDelta810c1 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 512 : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 128 * gamma : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (15 / 1024 * delta : k),
      (15 / 1024 * delta : k), (5 / 64 * delta : k), (-(15 / 64 * delta) : k),
      (-(15 / 128 * delta) : k), (5 / 8 * delta : k), (-(1 / 4 * epsilon) : k),
      (1 / 2 * epsilon : k), (5 / 1024 * zeta : k)]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0],
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [3, 0, 0, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestDelta810c1, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestDelta810c1_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp8 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp9 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree < 4 * A.natDegree) :
    (n2QuarticCostRestDelta810c1 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestDelta810c1_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestDelta810c2_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestDelta810c2 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (3 / 64 * zeta : k), (-(15 / 128 * zeta) : k), (3 / 8 * zeta : k),
      (1 / 4 * eta : k), (3 / 128 * theta : k), (1 / 8 * theta : k)]
      [
      [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
      [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestDelta810c2, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestDelta810c2_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp8 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp9 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree < 4 * A.natDegree) :
    (n2QuarticCostRestDelta810c2 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestDelta810c2_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestDelta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 4 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 4 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree)
    (hp8 : B.natDegree + E.natDegree < 4 * A.natDegree)
    (hp9 : C.natDegree + D.natDegree < 4 * A.natDegree)
    (hp10 : 3 * B.natDegree < 4 * A.natDegree) :
    (n2QuarticCostRestDelta810 0 0 gamma delta epsilon zeta eta theta A B C D E F G).natDegree <
      4 * A.natDegree := by
  simp only [n2QuarticCostRestDelta810]
  exact (natDegree_add_lt810 (n2QuarticCostRestDelta810c1_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10) (n2QuarticCostRestDelta810c2_natDegree_lt l beta gamma delta epsilon zeta eta theta hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10))

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `delta` column of `N₂` is its unique top: every
load-free monomial costs more than `5·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN2CostTopDelta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D.natDegree + G.natDegree < 4 * A.natDegree ∧
    E.natDegree + F.natDegree < 4 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 3 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 4 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 4 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 4 * A.natDegree ∧
    B.natDegree + E.natDegree < 4 * A.natDegree ∧
    C.natDegree + D.natDegree < 4 * A.natDegree ∧
    3 * B.natDegree < 4 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `zeta` column, with the lighter
pure-`A` loads set to zero: 19 monomials. -/
def n2QuarticCostRestZeta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (3 / 64 * zeta : k) • (A * C)
  - (15 / 128 * zeta : k) • B ^ 2
  + (3 / 8 * zeta : k) • E
  + (1 / 4 * eta : k) • D
  + (3 / 128 * theta : k) • A ^ 2
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₂` splits
into its pure-`A` `zeta` column `c·zeta·A^3` and the rest. -/
theorem degreeZeroN2Quartic810_eq_zetaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G =
      n2QuarticZetaFace810 zeta A +
        n2QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n2QuarticZetaFace810, n2QuarticCostRestZeta810,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestZeta810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestZeta810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 512 : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 128 * gamma : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (-(1 / 4 * epsilon) : k),
      (1 / 2 * epsilon : k), (3 / 64 * zeta : k), (-(15 / 128 * zeta) : k),
      (3 / 8 * zeta : k), (1 / 4 * eta : k), (3 / 128 * theta : k),
      (1 / 8 * theta : k)]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0],
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0],
      [0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestZeta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestZeta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 3 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 3 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < 2 * A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 3 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree)
    (hp8 : B.natDegree + E.natDegree < 3 * A.natDegree)
    (hp9 : C.natDegree + D.natDegree < 3 * A.natDegree)
    (hp10 : B.natDegree < A.natDegree)
    (hp11 : F.natDegree < 3 * A.natDegree)
    (hp12 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    (n2QuarticCostRestZeta810 0 0 gamma 0 epsilon zeta eta theta A B C D E F G).natDegree <
      3 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestZeta810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `zeta` column of `N₂` is its unique top: every
load-free monomial costs more than `7·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN2CostTopZeta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D.natDegree + G.natDegree < 3 * A.natDegree ∧
    E.natDegree + F.natDegree < 3 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < 2 * A.natDegree ∧
    2 * B.natDegree + F.natDegree < 3 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 3 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 3 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 3 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 3 * A.natDegree ∧
    B.natDegree + E.natDegree < 3 * A.natDegree ∧
    C.natDegree + D.natDegree < 3 * A.natDegree ∧
    B.natDegree < A.natDegree ∧
    F.natDegree < 3 * A.natDegree ∧
    B.natDegree + C.natDegree < 3 * A.natDegree

set_option maxHeartbeats 64000000 in
/-- `N₂` off its pure-`A` `theta` column, with the lighter
pure-`A` loads set to zero: 15 monomials. -/
def n2QuarticCostRestTheta810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (15 / 512 : k) • (A * B ^ 2 * D)
  + (35 / 512 : k) • (B ^ 3 * C)
  - (15 / 128 : k) • (B ^ 2 * F)
  - (15 / 64 : k) • (B * C * E)
  - (15 / 128 : k) • (B * D ^ 2)
  - (15 / 128 : k) • (C ^ 2 * D)
  + (5 / 16 : k) • (D * G)
  + (5 / 16 : k) • (E * F)
  + (5 / 128 * gamma : k) • B ^ 3
  - (3 / 16 * gamma : k) • (B * E)
  - (3 / 16 * gamma : k) • (C * D)
  - (1 / 4 * epsilon : k) • (B * C)
  + (1 / 2 * epsilon : k) • F
  + (1 / 4 * eta : k) • D
  + (1 / 8 * theta : k) • C

set_option maxHeartbeats 64000000 in
/-- Cone-free: with the lighter pure-`A` loads zero, `N₂` splits
into its pure-`A` `theta` column `c·theta·A^2` and the rest. -/
theorem degreeZeroN2Quartic810_eq_thetaCostColumn_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroN2Quartic810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G =
      n2QuarticThetaFace810 theta A +
        n2QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G := by
  simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810, degreeZeroKappaQuartic810, n2QuarticThetaFace810, n2QuarticCostRestTheta810,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero,
    zero_add, sub_zero, neg_zero, pow_one]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- Reflected monomial data for the cost-ladder degree bound. -/
private theorem astra810l_n2QuarticCostRestTheta810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    n2QuarticCostRestTheta810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 512 : k), (35 / 512 : k), (-(15 / 128) : k),
      (-(15 / 64) : k), (-(15 / 128) : k), (-(15 / 128) : k),
      (5 / 16 : k), (5 / 16 : k), (5 / 128 * gamma : k),
      (-(3 / 16 * gamma) : k), (-(3 / 16 * gamma) : k), (-(1 / 4 * epsilon) : k),
      (1 / 2 * epsilon : k), (1 / 4 * eta : k), (1 / 8 * theta : k)]
      [
      [1, 2, 0, 1, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0],
      [0, 3, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]] := by
  simp only [n2QuarticCostRestTheta810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 64000000 in
theorem n2QuarticCostRestTheta810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hp0 : D.natDegree + G.natDegree < 2 * A.natDegree)
    (hp1 : E.natDegree + F.natDegree < 2 * A.natDegree)
    (hp2 : 2 * B.natDegree + D.natDegree < A.natDegree)
    (hp3 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree)
    (hp4 : B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree)
    (hp5 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree)
    (hp6 : 2 * C.natDegree + D.natDegree < 2 * A.natDegree)
    (hp7 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp8 : B.natDegree + E.natDegree < 2 * A.natDegree)
    (hp9 : C.natDegree + D.natDegree < 2 * A.natDegree)
    (hp10 : 3 * B.natDegree < 2 * A.natDegree)
    (hp11 : F.natDegree < 2 * A.natDegree)
    (hp12 : B.natDegree + C.natDegree < 2 * A.natDegree)
    (hp13 : D.natDegree < 2 * A.natDegree) :
    (n2QuarticCostRestTheta810 0 0 gamma 0 epsilon 0 eta theta A B C D E F G).natDegree <
      2 * A.natDegree := by
  rw [astra810l_n2QuarticCostRestTheta810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, max_lt_iff]
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
/-- The pure-`A` `theta` column of `N₂` is its unique top: every
load-free monomial costs more than `9·a`, and every monomial of a
lighter load column without a pure-`A` monomial costs more than the
weight gap. -/
def QuarticN2CostTopTheta810 (A B C D E F G : k[X]) : Prop :=
  QuarticRatioConeA810 A B C D E F G ∧
    D.natDegree + G.natDegree < 2 * A.natDegree ∧
    E.natDegree + F.natDegree < 2 * A.natDegree ∧
    2 * B.natDegree + D.natDegree < A.natDegree ∧
    2 * B.natDegree + F.natDegree < 2 * A.natDegree ∧
    B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree ∧
    B.natDegree + 2 * D.natDegree < 2 * A.natDegree ∧
    2 * C.natDegree + D.natDegree < 2 * A.natDegree ∧
    3 * B.natDegree + C.natDegree < 2 * A.natDegree ∧
    B.natDegree + E.natDegree < 2 * A.natDegree ∧
    C.natDegree + D.natDegree < 2 * A.natDegree ∧
    3 * B.natDegree < 2 * A.natDegree ∧
    F.natDegree < 2 * A.natDegree ∧
    B.natDegree + C.natDegree < 2 * A.natDegree ∧
    D.natDegree < 2 * A.natDegree

/-! ### `N₂` cost-form monotonicity, kills and bands -/

set_option maxHeartbeats 64000000 in
/-- The `beta` column of `N₂` tops it only if the cheaper `l`
column does. -/
theorem quarticN2CostTopBeta810_imp_L810
    {A B C D E F G : k[X]}
    (h : QuarticN2CostTopBeta810 A B C D E F G) :
    QuarticN2CostTopL810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `delta` column of `N₂` tops it only if the cheaper `beta`
column does. -/
theorem quarticN2CostTopDelta810_imp_Beta810
    {A B C D E F G : k[X]}
    (h : QuarticN2CostTopDelta810 A B C D E F G) :
    QuarticN2CostTopBeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `zeta` column of `N₂` tops it only if the cheaper `delta`
column does. -/
theorem quarticN2CostTopZeta810_imp_Delta810
    {A B C D E F G : k[X]}
    (h : QuarticN2CostTopZeta810 A B C D E F G) :
    QuarticN2CostTopDelta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- The `theta` column of `N₂` tops it only if the cheaper `zeta`
column does. -/
theorem quarticN2CostTopTheta810_imp_Zeta810
    {A B C D E F G : k[X]}
    (h : QuarticN2CostTopTheta810 A B C D E F G) :
    QuarticN2CostTopZeta810 A B C D E F G := by
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13⟩ := h
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  exact ⟨hA, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `l` column tops `N₂` then
`l = 0`, because `natDegree N₂ ≤ 1·a < 6·a`. -/
theorem quarticSigmaN2Cost_l_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN2CostTopL810 A B C D E F G)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    l = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (231 / 4194304 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n2QuarticLFace810 l A).natDegree = 6 * A.natDegree := by
    simp only [n2QuarticLFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n2QuarticCostRestL810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7
  have hle := degreeZeroN2Quartic810_natDegree_le l beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_lCostColumn_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `beta` column tops `N₂` then
`beta = 0`, because `natDegree N₂ ≤ 1·a < 5·a`. -/
theorem quarticSigmaN2Cost_beta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN2CostTopBeta810 A B C D E F G)
    (hl0 : l = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    beta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (63 / 262144 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n2QuarticBetaFace810 beta A).natDegree = 5 * A.natDegree := by
    simp only [n2QuarticBetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n2QuarticCostRestBeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7
  subst hl0
  have hle := degreeZeroN2Quartic810_natDegree_le 0 beta gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_betaCostColumn_add_rest (l := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `delta` column tops `N₂` then
`delta = 0`, because `natDegree N₂ ≤ 1·a < 4·a`. -/
theorem quarticSigmaN2Cost_delta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN2CostTopDelta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    delta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (35 / 32768 * delta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n2QuarticDeltaFace810 delta A).natDegree = 4 * A.natDegree := by
    simp only [n2QuarticDeltaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n2QuarticCostRestDelta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10
  subst hl0
  subst hbeta0
  have hle := degreeZeroN2Quartic810_natDegree_le 0 0 gamma delta epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_deltaCostColumn_add_rest (l := 0) (beta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `zeta` column tops `N₂` then
`zeta = 0`, because `natDegree N₂ ≤ 1·a < 3·a`. -/
theorem quarticSigmaN2Cost_zeta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN2CostTopZeta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    zeta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (5 / 1024 * zeta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n2QuarticZetaFace810 zeta A).natDegree = 3 * A.natDegree := by
    simp only [n2QuarticZetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n2QuarticCostRestZeta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  subst hl0
  subst hbeta0
  subst hdelta0
  have hle := degreeZeroN2Quartic810_natDegree_le 0 0 gamma 0 epsilon zeta eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_zetaCostColumn_add_rest (l := 0) (beta := 0) (delta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-form kill: if the pure-`A` `theta` column tops `N₂` then
`theta = 0`, because `natDegree N₂ ≤ 1·a < 2·a`. -/
theorem quarticSigmaN2Cost_theta_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (htop : QuarticN2CostTopTheta810 A B C D E F G)
    (hl0 : l = 0)
    (hbeta0 : beta = 0)
    (hdelta0 : delta = 0)
    (hzeta0 : zeta = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    theta = 0 := by
  by_contra hne
  obtain ⟨hA, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13⟩ := htop
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hc : (3 / 128 * theta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hne
  have hlead : (n2QuarticThetaFace810 theta A).natDegree = 2 * A.natDegree := by
    simp only [n2QuarticThetaFace810]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest := n2QuarticCostRestTheta810_natDegree_lt l beta gamma delta epsilon zeta eta theta
    hApos hAB hAC hAD hAE hAF hAG hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13
  subst hl0
  subst hbeta0
  subst hdelta0
  subst hzeta0
  have hle := degreeZeroN2Quartic810_natDegree_le 0 0 gamma 0 epsilon 0 eta theta
    A B C D E F G hnu hkap
  rw [degreeZeroN2Quartic810_eq_thetaCostColumn_add_rest (l := 0) (beta := 0) (delta := 0) (zeta := 0),
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hle
  omega

set_option maxHeartbeats 64000000 in
theorem quarticSigmaN2Cost_l_band
    {l : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN2CostTopL810 A B C D E F G → l = 0) :
    l = 0 ∨
      6 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree := by
  by_cases hb0 : D.natDegree + G.natDegree < 6 * A.natDegree
  · by_cases hb1 : E.natDegree + F.natDegree < 6 * A.natDegree
    · by_cases hb2 : 2 * B.natDegree + D.natDegree < 5 * A.natDegree
      · by_cases hb3 : 2 * B.natDegree + F.natDegree < 6 * A.natDegree
        · by_cases hb4 : B.natDegree + C.natDegree + E.natDegree < 6 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * D.natDegree < 6 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + D.natDegree < 6 * A.natDegree
              · by_cases hb7 : 3 * B.natDegree + C.natDegree < 6 * A.natDegree
                · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩)
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))
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
theorem quarticSigmaN2Cost_beta_band
    {beta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN2CostTopBeta810 A B C D E F G → beta = 0) :
    beta = 0 ∨
      5 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree := by
  by_cases hb0 : D.natDegree + G.natDegree < 5 * A.natDegree
  · by_cases hb1 : E.natDegree + F.natDegree < 5 * A.natDegree
    · by_cases hb2 : 2 * B.natDegree + D.natDegree < 4 * A.natDegree
      · by_cases hb3 : 2 * B.natDegree + F.natDegree < 5 * A.natDegree
        · by_cases hb4 : B.natDegree + C.natDegree + E.natDegree < 5 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * D.natDegree < 5 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + D.natDegree < 5 * A.natDegree
              · by_cases hb7 : 3 * B.natDegree + C.natDegree < 5 * A.natDegree
                · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩)
                · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_))))))))
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
theorem quarticSigmaN2Cost_delta_band
    {delta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN2CostTopDelta810 A B C D E F G → delta = 0) :
    delta = 0 ∨
      4 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree := by
  by_cases hb0 : D.natDegree + G.natDegree < 4 * A.natDegree
  · by_cases hb1 : E.natDegree + F.natDegree < 4 * A.natDegree
    · by_cases hb2 : 2 * B.natDegree + D.natDegree < 3 * A.natDegree
      · by_cases hb3 : 2 * B.natDegree + F.natDegree < 4 * A.natDegree
        · by_cases hb4 : B.natDegree + C.natDegree + E.natDegree < 4 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * D.natDegree < 4 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + D.natDegree < 4 * A.natDegree
              · by_cases hb7 : 3 * B.natDegree + C.natDegree < 4 * A.natDegree
                · by_cases hb8 : B.natDegree + E.natDegree < 4 * A.natDegree
                  · by_cases hb9 : C.natDegree + D.natDegree < 4 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree < 4 * A.natDegree
                      · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩)
                      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))))
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
theorem quarticSigmaN2Cost_zeta_band
    {zeta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN2CostTopZeta810 A B C D E F G → zeta = 0) :
    zeta = 0 ∨
      3 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      3 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      3 * A.natDegree ≤ F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree := by
  by_cases hb0 : D.natDegree + G.natDegree < 3 * A.natDegree
  · by_cases hb1 : E.natDegree + F.natDegree < 3 * A.natDegree
    · by_cases hb2 : 2 * B.natDegree + D.natDegree < 2 * A.natDegree
      · by_cases hb3 : 2 * B.natDegree + F.natDegree < 3 * A.natDegree
        · by_cases hb4 : B.natDegree + C.natDegree + E.natDegree < 3 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * D.natDegree < 3 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + D.natDegree < 3 * A.natDegree
              · by_cases hb7 : 3 * B.natDegree + C.natDegree < 3 * A.natDegree
                · by_cases hb8 : B.natDegree + E.natDegree < 3 * A.natDegree
                  · by_cases hb9 : C.natDegree + D.natDegree < 3 * A.natDegree
                    · by_cases hb10 : B.natDegree < A.natDegree
                      · by_cases hb11 : F.natDegree < 3 * A.natDegree
                        · by_cases hb12 : B.natDegree + C.natDegree < 3 * A.natDegree
                          · exact Or.inl (hkill ⟨hA, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12⟩)
                          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (?_)))))))))))))
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
theorem quarticSigmaN2Cost_theta_band
    {theta : k} (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkill : QuarticN2CostTopTheta810 A B C D E F G → theta = 0) :
    theta = 0 ∨
      2 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      2 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree ∨
      2 * A.natDegree ≤ F.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + C.natDegree ∨
      2 * A.natDegree ≤ D.natDegree := by
  by_cases hb0 : D.natDegree + G.natDegree < 2 * A.natDegree
  · by_cases hb1 : E.natDegree + F.natDegree < 2 * A.natDegree
    · by_cases hb2 : 2 * B.natDegree + D.natDegree < A.natDegree
      · by_cases hb3 : 2 * B.natDegree + F.natDegree < 2 * A.natDegree
        · by_cases hb4 : B.natDegree + C.natDegree + E.natDegree < 2 * A.natDegree
          · by_cases hb5 : B.natDegree + 2 * D.natDegree < 2 * A.natDegree
            · by_cases hb6 : 2 * C.natDegree + D.natDegree < 2 * A.natDegree
              · by_cases hb7 : 3 * B.natDegree + C.natDegree < 2 * A.natDegree
                · by_cases hb8 : B.natDegree + E.natDegree < 2 * A.natDegree
                  · by_cases hb9 : C.natDegree + D.natDegree < 2 * A.natDegree
                    · by_cases hb10 : 3 * B.natDegree < 2 * A.natDegree
                      · by_cases hb11 : F.natDegree < 2 * A.natDegree
                        · by_cases hb12 : B.natDegree + C.natDegree < 2 * A.natDegree
                          · by_cases hb13 : D.natDegree < 2 * A.natDegree
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
/-- The cost-form `N₂` ladder as five band disjunctions. -/
theorem quarticSigmaN2CostBands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    (l = 0 ∨
      6 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      6 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      6 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      6 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      6 * A.natDegree ≤ 3 * B.natDegree + C.natDegree) ∧
    (beta = 0 ∨
      5 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      5 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      5 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      5 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      5 * A.natDegree ≤ 3 * B.natDegree + C.natDegree) ∧
    (delta = 0 ∨
      4 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      4 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      4 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      4 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      4 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      4 * A.natDegree ≤ 3 * B.natDegree) ∧
    (zeta = 0 ∨
      3 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      3 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      3 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      3 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      3 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      A.natDegree ≤ B.natDegree ∨
      3 * A.natDegree ≤ F.natDegree ∨
      3 * A.natDegree ≤ B.natDegree + C.natDegree) ∧
    (theta = 0 ∨
      2 * A.natDegree ≤ D.natDegree + G.natDegree ∨
      2 * A.natDegree ≤ E.natDegree + F.natDegree ∨
      A.natDegree ≤ 2 * B.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ 2 * B.natDegree + F.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + C.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + 2 * D.natDegree ∨
      2 * A.natDegree ≤ 2 * C.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree + C.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + E.natDegree ∨
      2 * A.natDegree ≤ C.natDegree + D.natDegree ∨
      2 * A.natDegree ≤ 3 * B.natDegree ∨
      2 * A.natDegree ≤ F.natDegree ∨
      2 * A.natDegree ≤ B.natDegree + C.natDegree ∨
      2 * A.natDegree ≤ D.natDegree) := by
  by_cases hTl : QuarticN2CostTopL810 A B C D E F G
  · have hl0 : l = 0 :=
      quarticSigmaN2Cost_l_eq_zero l beta gamma delta epsilon zeta eta theta
        A B C D E F G hTl hnu hkap
    by_cases hTbeta : QuarticN2CostTopBeta810 A B C D E F G
    · have hbeta0 : beta = 0 :=
        quarticSigmaN2Cost_beta_eq_zero l beta gamma delta epsilon zeta eta theta
          A B C D E F G hTbeta hl0 hnu hkap
      by_cases hTdelta : QuarticN2CostTopDelta810 A B C D E F G
      · have hdelta0 : delta = 0 :=
          quarticSigmaN2Cost_delta_eq_zero l beta gamma delta epsilon zeta eta theta
            A B C D E F G hTdelta hl0 hbeta0 hnu hkap
        by_cases hTzeta : QuarticN2CostTopZeta810 A B C D E F G
        · have hzeta0 : zeta = 0 :=
            quarticSigmaN2Cost_zeta_eq_zero l beta gamma delta epsilon zeta eta theta
              A B C D E F G hTzeta hl0 hbeta0 hdelta0 hnu hkap
          by_cases hTtheta : QuarticN2CostTopTheta810 A B C D E F G
          · have htheta0 : theta = 0 :=
              quarticSigmaN2Cost_theta_eq_zero l beta gamma delta epsilon zeta eta theta
                A B C D E F G hTtheta hl0 hbeta0 hdelta0 hzeta0 hnu hkap
            exact ⟨Or.inl hl0, Or.inl hbeta0, Or.inl hdelta0, Or.inl hzeta0, Or.inl htheta0⟩
          · exact ⟨Or.inl hl0,
              Or.inl hbeta0,
              Or.inl hdelta0,
              Or.inl hzeta0,
              quarticSigmaN2Cost_theta_band (theta := theta) A B C D E F G hA
                (fun htop => absurd (htop) hTtheta)⟩
        · exact ⟨Or.inl hl0,
            Or.inl hbeta0,
            Or.inl hdelta0,
            quarticSigmaN2Cost_zeta_band (zeta := zeta) A B C D E F G hA
              (fun htop => absurd (htop) hTzeta),
            quarticSigmaN2Cost_theta_band (theta := theta) A B C D E F G hA
              (fun htop => absurd (quarticN2CostTopTheta810_imp_Zeta810 (htop)) hTzeta)⟩
      · exact ⟨Or.inl hl0,
          Or.inl hbeta0,
          quarticSigmaN2Cost_delta_band (delta := delta) A B C D E F G hA
            (fun htop => absurd (htop) hTdelta),
          quarticSigmaN2Cost_zeta_band (zeta := zeta) A B C D E F G hA
            (fun htop => absurd (quarticN2CostTopZeta810_imp_Delta810 (htop)) hTdelta),
          quarticSigmaN2Cost_theta_band (theta := theta) A B C D E F G hA
            (fun htop => absurd (quarticN2CostTopZeta810_imp_Delta810 (quarticN2CostTopTheta810_imp_Zeta810 (htop))) hTdelta)⟩
    · exact ⟨Or.inl hl0,
        quarticSigmaN2Cost_beta_band (beta := beta) A B C D E F G hA
          (fun htop => absurd (htop) hTbeta),
        quarticSigmaN2Cost_delta_band (delta := delta) A B C D E F G hA
          (fun htop => absurd (quarticN2CostTopDelta810_imp_Beta810 (htop)) hTbeta),
        quarticSigmaN2Cost_zeta_band (zeta := zeta) A B C D E F G hA
          (fun htop => absurd (quarticN2CostTopDelta810_imp_Beta810 (quarticN2CostTopZeta810_imp_Delta810 (htop))) hTbeta),
        quarticSigmaN2Cost_theta_band (theta := theta) A B C D E F G hA
          (fun htop => absurd (quarticN2CostTopDelta810_imp_Beta810 (quarticN2CostTopZeta810_imp_Delta810 (quarticN2CostTopTheta810_imp_Zeta810 (htop)))) hTbeta)⟩
  · exact ⟨quarticSigmaN2Cost_l_band (l := l) A B C D E F G hA
        (fun htop => absurd (htop) hTl),
      quarticSigmaN2Cost_beta_band (beta := beta) A B C D E F G hA
        (fun htop => absurd (quarticN2CostTopBeta810_imp_L810 (htop)) hTl),
      quarticSigmaN2Cost_delta_band (delta := delta) A B C D E F G hA
        (fun htop => absurd (quarticN2CostTopBeta810_imp_L810 (quarticN2CostTopDelta810_imp_Beta810 (htop))) hTl),
      quarticSigmaN2Cost_zeta_band (zeta := zeta) A B C D E F G hA
        (fun htop => absurd (quarticN2CostTopBeta810_imp_L810 (quarticN2CostTopDelta810_imp_Beta810 (quarticN2CostTopZeta810_imp_Delta810 (htop)))) hTl),
      quarticSigmaN2Cost_theta_band (theta := theta) A B C D E F G hA
        (fun htop => absurd (quarticN2CostTopBeta810_imp_L810 (quarticN2CostTopDelta810_imp_Beta810 (quarticN2CostTopZeta810_imp_Delta810 (quarticN2CostTopTheta810_imp_Zeta810 (htop))))) hTl)⟩


end QuarticCostLadder810

end Max11DegreeRoutes
