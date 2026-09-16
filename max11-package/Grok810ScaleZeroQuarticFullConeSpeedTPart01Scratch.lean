import Grok810ScaleZeroQuarticFullConeSpeedTPart00Scratch

/-! # Full 7-letter cone `R = {A,B,C,D,E,F,G}` of normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroQuarticConesScratch`.  That file exports
`normalized810ScaleZero_quarticADominantResidual` whose last conjunct is
`QuarticRatioConeA810 ∨ QuarticRatioConeABCDEFG810`.  This file treats the
ABCDEFG branch only.

CAS (Singular, weighted grevlex, Rabinowitsch `T·abcdefg-1`): the saturated
load-free ideal on this cone is `(1)`.  The Groebner basis contains `g^7`
and `c d f² g²`.  Explicit lift multipliers have ~300-digit coefficients,
too large for Lean `ring`.  Lean has the G-eliminating Sylvester cores
(plan §6) and the next a-resultant layer: 2×2 identities of the cores
linear in `a`, the deg-1/deg-2 Sylvester of `ν` against `ο`, and the
weight-26 combination `R_ο − 10 b⁴ d R_{μν} = 8 b⁶ d T` whose factor `T`
is linear in `e`.  The remaining Groebner `(1)` certificate among the
e-free faces is not transcribed.

No `sorry`, no new axioms, no finite-root shortcut.  Untracked working
note.
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

section QuarticFullConeABCDEFG810

variable {k : Type*} [Field k] [CharZero k]


set_option maxHeartbeats 64000000 in
def piQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (15 / 4096 : k) • (A ^ 2 * B ^ 4)
  - (15 / 128 : k) • (A * B ^ 3 * D)
  - (45 / 512 : k) • (A * B ^ 2 * C ^ 2)
  - (35 / 256 : k) • (B ^ 4 * C)
  + (5 / 64 : k) • (A * B ^ 2 * G)
  + (5 / 32 : k) • (A * B * C * F)
  + (5 / 16 : k) • (A * B * D * E)
  + (5 / 32 : k) • (A * C * D ^ 2)
  + (25 / 128 : k) • (B ^ 3 * F)
  + (45 / 64 : k) • (B ^ 2 * C * E)
  + (45 / 128 : k) • (B ^ 2 * D ^ 2)
  + (45 / 64 : k) • (B * C ^ 2 * D)
  + (15 / 256 : k) • C ^ 4
  - (5 / 16 : k) • (A * F ^ 2)
  - (5 / 8 : k) • (B * D * G)
  - (15 / 16 : k) • (B * E * F)
  - (5 / 16 : k) • (C ^ 2 * G)
  - (15 / 16 : k) • (C * D * F)
  - (5 / 8 : k) • (C * E ^ 2)
  - (5 / 8 : k) • (D ^ 2 * E)
  + (5 / 4 : k) • G ^ 2

set_option maxHeartbeats 64000000 in
def degreeZeroPiQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (45 / 131072 * l : k) • (A ^ 4 * B * C)
  - (3 / 32768 * l : k) • (A ^ 3 * B ^ 3)
  - (45 / 32768 * l : k) • (A ^ 4 * F)
  + (9 / 4096 * l : k) • (A ^ 3 * B * E)
  + (9 / 4096 * l : k) • (A ^ 3 * C * D)
  - (27 / 4096 * l : k) • (A ^ 2 * B ^ 2 * D)
  + (9 / 4096 * l : k) • (A ^ 2 * B * C ^ 2)
  - (189 / 4096 * l : k) • (A * B ^ 3 * C)
  - (63 / 4096 * l : k) • B ^ 5
  - (27 / 1024 * l : k) • (A ^ 2 * C * F)
  + (9 / 512 * l : k) • (A ^ 2 * D * E)
  + (63 / 1024 * l : k) • (A * B ^ 2 * F)
  + (9 / 128 * l : k) • (A * B * C * E)
  + (27 / 256 * l : k) • (A * B * D ^ 2)
  + (9 / 256 * l : k) • (A * C ^ 2 * D)
  + (63 / 512 * l : k) • (B ^ 3 * E)
  + (189 / 512 * l : k) • (B ^ 2 * C * D)
  + (63 / 512 * l : k) • (B * C ^ 3)
  - (9 / 64 * l : k) • (A * E * F)
  - (9 / 32 * l : k) • (B * C * G)
  - (27 / 64 * l : k) • (B * D * F)
  - (9 / 32 * l : k) • (B * E ^ 2)
  - (27 / 128 * l : k) • (C ^ 2 * F)
  - (9 / 16 * l : k) • (C * D * E)
  - (3 / 32 * l : k) • D ^ 3
  + (9 / 8 * l : k) • (F * G)
  + (7 / 4096 * beta : k) • (A ^ 3 * B * C)
  + (7 / 4096 * beta : k) • (A ^ 2 * B ^ 3)
  - (7 / 1024 * beta : k) • (A ^ 3 * F)
  + (7 / 512 * beta : k) • (A ^ 2 * B * E)
  + (7 / 512 * beta : k) • (A ^ 2 * C * D)
  - (21 / 256 * beta : k) • (A * B ^ 2 * D)
  - (7 / 256 * beta : k) • (A * B * C ^ 2)
  - (63 / 512 * beta : k) • (B ^ 3 * C)
  - (7 / 64 * beta : k) • (A * C * F)
  + (7 / 32 * beta : k) • (A * D * E)
  + (21 / 128 * beta : k) • (B ^ 2 * F)
  + (7 / 16 * beta : k) • (B * C * E)
  + (7 / 32 * beta : k) • (B * D ^ 2)
  + (7 / 32 * beta : k) • (C ^ 2 * D)
  - (7 / 8 * beta : k) • (E * F)
  - (3 / 32 * gamma : k) • (A * B ^ 2 * C)
  - (15 / 256 * gamma : k) • B ^ 4
  + (3 / 16 * gamma : k) • (A * D ^ 2)
  + (3 / 8 * gamma : k) • (B ^ 2 * E)
  + (3 / 4 * gamma : k) • (B * C * D)
  + (1 / 8 * gamma : k) • C ^ 3
  - (3 / 4 * gamma : k) • (D * F)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 512 * delta : k) • (A ^ 2 * B * C)
  - (15 / 256 * delta : k) • (A * B ^ 3)
  - (5 / 128 * delta : k) • (A ^ 2 * F)
  + (5 / 32 * delta : k) • (A * B * E)
  + (5 / 32 * delta : k) • (A * C * D)
  + (15 / 32 * delta : k) • (B ^ 2 * D)
  + (15 / 32 * delta : k) • (B * C ^ 2)
  - (5 / 8 * delta : k) • (C * F)
  - (5 / 4 * delta : k) • (D * E)
  + (1 / 4 * epsilon : k) • (A * B * D)
  + (1 / 2 * epsilon : k) • (B ^ 2 * C)
  - (1 / 2 * epsilon : k) • (B * F)
  - (1 * epsilon : k) • (C * E)
  - (1 / 2 * epsilon : k) • D ^ 2
  + (3 / 32 * zeta : k) • (A * B * C)
  + (5 / 32 * zeta : k) • B ^ 3
  - (3 / 8 * zeta : k) • (A * F)
  - (3 / 4 * zeta : k) • (B * E)
  - (3 / 4 * zeta : k) • (C * D)
  + (1 / 16 * eta : k) • (A * B ^ 2)
  - (1 / 2 * eta : k) • (B * D)
  - (1 / 4 * eta : k) • C ^ 2
  + (2 * eta : k) • G
  - (1 / 4 * theta : k) • (B * C)
  + (1 * theta : k) • F

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroPiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABCDEFG810, degreeZeroPiQuarticNoABCDEFG810]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, mul_neg, neg_mul, neg_smul, sub_eq_add_neg, mul_comm, mul_one, one_mul, one_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPiQuarticNoABCDEFG810` (74 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (45 / 131072 * l : k), (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k),
      (9 / 4096 * l : k), (9 / 4096 * l : k), (-(27 / 4096 * l) : k),
      (9 / 4096 * l : k), (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k),
      (-(27 / 1024 * l) : k), (9 / 512 * l : k), (63 / 1024 * l : k),
      (9 / 128 * l : k), (27 / 256 * l : k), (9 / 256 * l : k),
      (63 / 512 * l : k), (189 / 512 * l : k), (63 / 512 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k), (-(27 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(27 / 128 * l) : k), (-(9 / 16 * l) : k),
      (-(3 / 32 * l) : k), (9 / 8 * l : k), (7 / 4096 * beta : k),
      (7 / 4096 * beta : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (7 / 512 * beta : k), (-(21 / 256 * beta) : k), (-(7 / 256 * beta) : k),
      (-(63 / 512 * beta) : k), (-(7 / 64 * beta) : k), (7 / 32 * beta : k),
      (21 / 128 * beta : k), (7 / 16 * beta : k), (7 / 32 * beta : k),
      (7 / 32 * beta : k), (-(7 / 8 * beta) : k), (-(3 / 32 * gamma) : k),
      (-(15 / 256 * gamma) : k), (3 / 16 * gamma : k), (3 / 8 * gamma : k),
      (3 / 4 * gamma : k), (1 / 8 * gamma : k), (-(3 / 4 * gamma) : k),
      (-(3 / 4 * gamma) : k), (5 / 512 * delta : k), (-(15 / 256 * delta) : k),
      (-(5 / 128 * delta) : k), (5 / 32 * delta : k), (5 / 32 * delta : k),
      (15 / 32 * delta : k), (15 / 32 * delta : k), (-(5 / 8 * delta) : k),
      (-(5 / 4 * delta) : k), (1 / 4 * epsilon : k), (1 / 2 * epsilon : k),
      (-(1 / 2 * epsilon) : k), (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k),
      (3 / 32 * zeta : k), (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k),
      (-(3 / 4 * zeta) : k), (-(3 / 4 * zeta) : k), (1 / 16 * eta : k),
      (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k), (2 * eta : k),
      (-(1 / 4 * theta) : k), (1 * theta : k)]
      [
      [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0],
      [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0],
      [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0],
      [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0],
      [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1],
      [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0],
      [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0],
      [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0],
      [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0],
      [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0],
      [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0],
      [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0],
      [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1],
      [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroPiQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroPiQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem piQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceABCDEFG810 A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) =
      (1 / 4096 : k) * piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [piQuarticFaceABCDEFG810, piQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B4 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B4 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hdeg_A2B4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3D : ((A * B ^ 3 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB3D : ((A * B ^ 3 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_AB3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2C2 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB2C2 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_AB2C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB2G : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB2G : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_AB2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCF : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABCF : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABCF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABDE : ((A * B * D * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABDE : ((A * B * D * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ABDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ACD2 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ACD2 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_ACD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4C : ((B ^ 4 * C)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B4C : ((B ^ 4 * C)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 4 * C.leadingCoeff := by
    rw [← hdeg_B4C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CE : ((B ^ 2 * C * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2CE : ((B ^ 2 * C * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2CE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BC2D : ((B * C ^ 2 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BC2D : ((B * C ^ 2 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_BC2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BDG : ((B * D * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BEF : ((B * E * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hFne, natDegree_mul hBne hEne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BEF : ((B * E * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_BEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDF : ((C * D * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hFne, natDegree_mul hCne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CDF : ((C * D * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CE2 : ((C * E ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CE2 : ((C * E ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_CE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2E : ((D ^ 2 * E)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hEne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_D2E : ((D ^ 2 * E)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      D.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_D2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_G2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2B4, hcf_AB3D, hcf_AB2C2, hcf_AB2G, hcf_ABCF, hcf_ABDE, hcf_ACD2, hcf_AF2, hcf_B4C, hcf_B3F, hcf_B2CE, hcf_B2D2, hcf_BC2D, hcf_BDG, hcf_BEF, hcf_C4, hcf_C2G, hcf_CDF, hcf_CE2, hcf_D2E, hcf_G2]
  ring

set_option maxHeartbeats 64000000 in
def primitiveQuarticFaceABCDEFG810 (A B C D E F G : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3)
  - (15 / 16384 : k) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)
  + (5 / 128 : k) • (A * B * C * G)
  + (5 / 32 : k) • (A * B * D * F)
  + (5 / 64 : k) • (A * B * E ^ 2)
  + (15 / 128 : k) • (A * C * D * E)
  + (5 / 128 : k) • (A * D ^ 3)
  + (15 / 256 : k) • (B ^ 3 * G)
  + (85 / 256 : k) • (B ^ 2 * C * F)
  + (85 / 256 : k) • (B ^ 2 * D * E)
  + (45 / 128 : k) • (B * C ^ 2 * E)
  + (45 / 128 : k) • (B * C * D ^ 2)
  + (15 / 128 : k) • (C ^ 3 * D)
  - (5 / 16 : k) • (A * F * G)
  - (5 / 16 : k) • (B * E * G)
  - (5 / 16 : k) • (B * F ^ 2)
  - (5 / 16 : k) • (C * D * G)
  - (5 / 8 : k) • (C * E * F)
  - (5 / 16 : k) • (D ^ 2 * F)
  - (5 / 16 : k) • (D * E ^ 2)

set_option maxHeartbeats 64000000 in
def degreeZeroPrimitiveQuarticNoABCDEFG810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  (1575 / 268435456 * l : k) • A ^ 8
  + (765 / 4194304 * l : k) • (A ^ 6 * C)
  - (369 / 4194304 * l : k) • (A ^ 5 * B ^ 2)
  + (171 / 262144 * l : k) • (A ^ 5 * E)
  - (153 / 262144 * l : k) • (A ^ 4 * B * D)
  + (855 / 524288 * l : k) • (A ^ 4 * C ^ 2)
  - (81 / 131072 * l : k) • (A ^ 3 * B ^ 2 * C)
  + (261 / 262144 * l : k) • (A ^ 2 * B ^ 4)
  + (45 / 32768 * l : k) • (A ^ 4 * G)
  - (9 / 4096 * l : k) • (A ^ 3 * B * F)
  + (99 / 8192 * l : k) • (A ^ 3 * C * E)
  - (9 / 4096 * l : k) • (A ^ 3 * D ^ 2)
  - (9 / 4096 * l : k) • (A ^ 2 * B ^ 2 * E)
  + (9 / 8192 * l : k) • (A ^ 2 * B * C * D)
  + (27 / 16384 * l : k) • (A ^ 2 * C ^ 3)
  - (243 / 8192 * l : k) • (A * B ^ 3 * D)
  - (387 / 16384 * l : k) • (A * B ^ 2 * C ^ 2)
  - (567 / 16384 * l : k) • (B ^ 4 * C)
  + (27 / 1024 * l : k) • (A ^ 2 * C * G)
  - (9 / 512 * l : k) • (A ^ 2 * D * F)
  + (27 / 1024 * l : k) • (A ^ 2 * E ^ 2)
  + (9 / 1024 * l : k) • (A * B ^ 2 * G)
  + (9 / 256 * l : k) • (A * B * C * F)
  + (45 / 512 * l : k) • (A * B * D * E)
  + (9 / 1024 * l : k) • (A * C ^ 2 * E)
  + (9 / 256 * l : k) • (A * C * D ^ 2)
  + (27 / 512 * l : k) • (B ^ 3 * F)
  + (45 / 256 * l : k) • (B ^ 2 * C * E)
  + (45 / 512 * l : k) • (B ^ 2 * D ^ 2)
  + (189 / 1024 * l : k) • (B * C ^ 2 * D)
  + (63 / 4096 * l : k) • C ^ 4
  + (9 / 64 * l : k) • (A * E * G)
  - (9 / 64 * l : k) • (A * F ^ 2)
  - (9 / 64 * l : k) • (B * D * G)
  - (9 / 32 * l : k) • (B * E * F)
  - (9 / 128 * l : k) • (C ^ 2 * G)
  - (9 / 32 * l : k) • (C * D * F)
  - (9 / 64 * l : k) • (C * E ^ 2)
  - (9 / 64 * l : k) • (D ^ 2 * E)
  + (9 / 16 * l : k) • G ^ 2
  + (25 / 1048576 * beta : k) • A ^ 7
  + (21 / 32768 * beta : k) • (A ^ 5 * C)
  - (119 / 262144 * beta : k) • (A ^ 4 * B ^ 2)
  + (35 / 16384 * beta : k) • (A ^ 4 * E)
  - (7 / 2048 * beta : k) • (A ^ 3 * B * D)
  + (21 / 4096 * beta : k) • (A ^ 3 * C ^ 2)
  - (21 / 8192 * beta : k) • (A ^ 2 * B ^ 2 * C)
  + (119 / 16384 * beta : k) • (A * B ^ 4)
  + (21 / 512 * beta : k) • (A ^ 2 * C * E)
  - (7 / 512 * beta : k) • (A ^ 2 * D ^ 2)
  - (21 / 512 * beta : k) • (A * B ^ 2 * E)
  - (7 / 128 * beta : k) • (A * B * C * D)
  - (7 / 128 * beta : k) • (B ^ 3 * D)
  - (91 / 1024 * beta : k) • (B ^ 2 * C ^ 2)
  + (7 / 64 * beta : k) • (A * E ^ 2)
  + (7 / 32 * beta : k) • (B * C * F)
  + (7 / 32 * beta : k) • (B * D * E)
  + (7 / 64 * beta : k) • (C ^ 2 * E)
  + (7 / 64 * beta : k) • (C * D ^ 2)
  - (7 / 16 * beta : k) • F ^ 2
  + (3 / 2048 * gamma : k) • (A ^ 3 * B * C)
  + (3 / 2048 * gamma : k) • (A ^ 2 * B ^ 3)
  - (3 / 512 * gamma : k) • (A ^ 3 * F)
  + (3 / 256 * gamma : k) • (A ^ 2 * B * E)
  + (3 / 256 * gamma : k) • (A ^ 2 * C * D)
  - (9 / 128 * gamma : k) • (A * B ^ 2 * D)
  - (3 / 128 * gamma : k) • (A * B * C ^ 2)
  - (27 / 256 * gamma : k) • (B ^ 3 * C)
  - (3 / 32 * gamma : k) • (A * C * F)
  + (3 / 16 * gamma : k) • (A * D * E)
  + (9 / 64 * gamma : k) • (B ^ 2 * F)
  + (3 / 8 * gamma : k) • (B * C * E)
  + (3 / 16 * gamma : k) • (B * D ^ 2)
  + (3 / 16 * gamma : k) • (C ^ 2 * D)
  - (3 / 4 * gamma : k) • (E * F)
  + (25 / 262144 * delta : k) • A ^ 6
  + (35 / 16384 * delta : k) • (A ^ 4 * C)
  - (25 / 16384 * delta : k) • (A ^ 3 * B ^ 2)
  + (5 / 1024 * delta : k) • (A ^ 3 * E)
  - (5 / 512 * delta : k) • (A ^ 2 * B * D)
  + (15 / 1024 * delta : k) • (A ^ 2 * C ^ 2)
  - (65 / 1024 * delta : k) • (A * B ^ 2 * C)
  - (135 / 4096 * delta : k) • B ^ 4
  + (5 / 64 * delta : k) • (A * C * E)
  + (5 / 64 * delta : k) • (A * D ^ 2)
  + (25 / 128 * delta : k) • (B ^ 2 * E)
  + (15 / 32 * delta : k) • (B * C * D)
  + (5 / 64 * delta : k) • C ^ 3
  - (5 / 8 * delta : k) • (D * F)
  - (5 / 16 * delta : k) • E ^ 2
  - (1 / 256 * epsilon : k) • (A ^ 3 * D)
  + (1 / 64 * epsilon : k) • (A ^ 2 * B * C)
  - (1 / 32 * epsilon : k) • (A * B ^ 3)
  - (1 / 32 * epsilon : k) • (A ^ 2 * F)
  + (1 / 8 * epsilon : k) • (A * B * E)
  + (1 / 16 * epsilon : k) • (A * C * D)
  + (7 / 32 * epsilon : k) • (B ^ 2 * D)
  + (1 / 4 * epsilon : k) • (B * C ^ 2)
  - (1 / 2 * epsilon : k) • (C * F)
  - (1 / 2 * epsilon : k) • (D * E)
  + (3 / 8192 * zeta : k) • A ^ 5
  + (3 / 512 * zeta : k) • (A ^ 3 * C)
  - (3 / 2048 * zeta : k) • (A ^ 2 * B ^ 2)
  + (3 / 128 * zeta : k) • (A ^ 2 * E)
  + (3 / 32 * zeta : k) • (A * B * D)
  + (27 / 128 * zeta : k) • (B ^ 2 * C)
  - (3 / 8 * zeta : k) • (B * F)
  - (3 / 8 * zeta : k) • (C * E)
  - (3 / 16 * zeta : k) • D ^ 2
  - (1 / 512 * eta : k) • (A ^ 3 * B)
  - (1 / 64 * eta : k) • (A ^ 2 * D)
  + (1 / 32 * eta : k) • (A * B * C)
  + (3 / 64 * eta : k) • B ^ 3
  - (1 / 4 * eta : k) • (A * F)
  - (1 / 4 * eta : k) • (B * E)
  - (1 / 4 * eta : k) • (C * D)
  + (5 / 4096 * theta : k) • A ^ 4
  + (3 / 128 * theta : k) • (A ^ 2 * C)
  + (1 / 128 * theta : k) • (A * B ^ 2)
  + (1 / 8 * theta : k) • (A * E)
  - (1 / 8 * theta : k) • (B * D)
  - (1 / 16 * theta : k) • C ^ 2
  + (1 * theta : k) • G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_ABCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      primitiveQuarticFaceABCDEFG810 A B C D E F G +
        degreeZeroPrimitiveQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810,
    rhoEpsilonGroupQuartic810, rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810, primitiveQuarticFaceABCDEFG810, degreeZeroPrimitiveQuarticNoABCDEFG810]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, mul_neg, neg_mul, neg_smul, sub_eq_add_neg, mul_comm, mul_one, one_mul, one_smul, add_assoc]

set_option maxHeartbeats 64000000 in
/-- Reflected form of `degreeZeroPrimitiveQuarticNoABCDEFG810` (123 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPrimitiveQuarticNoABCDEFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (1575 / 268435456 * l : k), (765 / 4194304 * l : k), (-(369 / 4194304 * l) : k),
      (171 / 262144 * l : k), (-(153 / 262144 * l) : k), (855 / 524288 * l : k),
      (-(81 / 131072 * l) : k), (261 / 262144 * l : k), (45 / 32768 * l : k),
      (-(9 / 4096 * l) : k), (99 / 8192 * l : k), (-(9 / 4096 * l) : k),
      (-(9 / 4096 * l) : k), (9 / 8192 * l : k), (27 / 16384 * l : k),
      (-(243 / 8192 * l) : k), (-(387 / 16384 * l) : k), (-(567 / 16384 * l) : k),
      (27 / 1024 * l : k), (-(9 / 512 * l) : k), (27 / 1024 * l : k),
      (9 / 1024 * l : k), (9 / 256 * l : k), (45 / 512 * l : k),
      (9 / 1024 * l : k), (9 / 256 * l : k), (27 / 512 * l : k),
      (45 / 256 * l : k), (45 / 512 * l : k), (189 / 1024 * l : k),
      (63 / 4096 * l : k), (9 / 64 * l : k), (-(9 / 64 * l) : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k), (-(9 / 128 * l) : k),
      (-(9 / 32 * l) : k), (-(9 / 64 * l) : k), (-(9 / 64 * l) : k),
      (9 / 16 * l : k), (25 / 1048576 * beta : k), (21 / 32768 * beta : k),
      (-(119 / 262144 * beta) : k), (35 / 16384 * beta : k), (-(7 / 2048 * beta) : k),
      (21 / 4096 * beta : k), (-(21 / 8192 * beta) : k), (119 / 16384 * beta : k),
      (21 / 512 * beta : k), (-(7 / 512 * beta) : k), (-(21 / 512 * beta) : k),
      (-(7 / 128 * beta) : k), (-(7 / 128 * beta) : k), (-(91 / 1024 * beta) : k),
      (7 / 64 * beta : k), (7 / 32 * beta : k), (7 / 32 * beta : k),
      (7 / 64 * beta : k), (7 / 64 * beta : k), (-(7 / 16 * beta) : k),
      (3 / 2048 * gamma : k), (3 / 2048 * gamma : k), (-(3 / 512 * gamma) : k),
      (3 / 256 * gamma : k), (3 / 256 * gamma : k), (-(9 / 128 * gamma) : k),
      (-(3 / 128 * gamma) : k), (-(27 / 256 * gamma) : k), (-(3 / 32 * gamma) : k),
      (3 / 16 * gamma : k), (9 / 64 * gamma : k), (3 / 8 * gamma : k),
      (3 / 16 * gamma : k), (3 / 16 * gamma : k), (-(3 / 4 * gamma) : k),
      (25 / 262144 * delta : k), (35 / 16384 * delta : k), (-(25 / 16384 * delta) : k),
      (5 / 1024 * delta : k), (-(5 / 512 * delta) : k), (15 / 1024 * delta : k),
      (-(65 / 1024 * delta) : k), (-(135 / 4096 * delta) : k), (5 / 64 * delta : k),
      (5 / 64 * delta : k), (25 / 128 * delta : k), (15 / 32 * delta : k),
      (5 / 64 * delta : k), (-(5 / 8 * delta) : k), (-(5 / 16 * delta) : k),
      (-(1 / 256 * epsilon) : k), (1 / 64 * epsilon : k), (-(1 / 32 * epsilon) : k),
      (-(1 / 32 * epsilon) : k), (1 / 8 * epsilon : k), (1 / 16 * epsilon : k),
      (7 / 32 * epsilon : k), (1 / 4 * epsilon : k), (-(1 / 2 * epsilon) : k),
      (-(1 / 2 * epsilon) : k), (3 / 8192 * zeta : k), (3 / 512 * zeta : k),
      (-(3 / 2048 * zeta) : k), (3 / 128 * zeta : k), (3 / 32 * zeta : k),
      (27 / 128 * zeta : k), (-(3 / 8 * zeta) : k), (-(3 / 8 * zeta) : k),
      (-(3 / 16 * zeta) : k), (-(1 / 512 * eta) : k), (-(1 / 64 * eta) : k),
      (1 / 32 * eta : k), (3 / 64 * eta : k), (-(1 / 4 * eta) : k),
      (-(1 / 4 * eta) : k), (-(1 / 4 * eta) : k), (5 / 4096 * theta : k),
      (3 / 128 * theta : k), (1 / 128 * theta : k), (1 / 8 * theta : k),
      (-(1 / 8 * theta) : k), (-(1 / 16 * theta) : k), (1 * theta : k)]
      [
      [8, 0, 0, 0, 0, 0, 0], [6, 0, 1, 0, 0, 0, 0], [5, 2, 0, 0, 0, 0, 0], [5, 0, 0, 0, 1, 0, 0],
      [4, 1, 0, 1, 0, 0, 0], [4, 0, 2, 0, 0, 0, 0], [3, 2, 1, 0, 0, 0, 0], [2, 4, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 1], [3, 1, 0, 0, 0, 1, 0], [3, 0, 1, 0, 1, 0, 0], [3, 0, 0, 2, 0, 0, 0],
      [2, 2, 0, 0, 1, 0, 0], [2, 1, 1, 1, 0, 0, 0], [2, 0, 3, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0],
      [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 1], [2, 0, 0, 1, 0, 1, 0],
      [2, 0, 0, 0, 2, 0, 0], [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 2, 0, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0], [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0],
      [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1],
      [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [0, 0, 0, 0, 0, 0, 2],
      [7, 0, 0, 0, 0, 0, 0], [5, 0, 1, 0, 0, 0, 0], [4, 2, 0, 0, 0, 0, 0], [4, 0, 0, 0, 1, 0, 0],
      [3, 1, 0, 1, 0, 0, 0], [3, 0, 2, 0, 0, 0, 0], [2, 2, 1, 0, 0, 0, 0], [1, 4, 0, 0, 0, 0, 0],
      [2, 0, 1, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0], [1, 2, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0],
      [0, 3, 0, 1, 0, 0, 0], [0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 0, 2, 0, 0], [0, 1, 1, 0, 0, 1, 0],
      [0, 1, 0, 1, 1, 0, 0], [0, 0, 2, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0],
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [6, 0, 0, 0, 0, 0, 0],
      [4, 0, 1, 0, 0, 0, 0], [3, 2, 0, 0, 0, 0, 0], [3, 0, 0, 0, 1, 0, 0], [2, 1, 0, 1, 0, 0, 0],
      [2, 0, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [3, 0, 0, 1, 0, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [5, 0, 0, 0, 0, 0, 0], [3, 0, 1, 0, 0, 0, 0], [2, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [3, 1, 0, 0, 0, 0, 0], [2, 0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0],
      [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0],
      [4, 0, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0],
      [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1]] := by
  simp only [degreeZeroPrimitiveQuarticNoABCDEFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  simp only [sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuarticNoABCDEFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABCDEFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  rw [speedRefl_degreeZeroPrimitiveQuarticNoABCDEFG810_eq_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    Nat.mul_one, Nat.one_mul, max_lt_iff]
  clear * - hApos hAB hAC hAD hAE hAF hAG
  repeat' apply And.intro
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticFaceABCDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceABCDEFG810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
  simp only [primitiveQuarticFaceABCDEFG810, primitiveQuarticInnerABCDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A4B3 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A4B3 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A4B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3B2D : ((A ^ 3 * B ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A3B2D : ((A ^ 3 * B ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A3B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BC2 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A3BC2 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A3BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BG : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A3BG : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A3BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3CF : ((A ^ 3 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A3CF : ((A ^ 3 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A3CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2B3C : ((A ^ 2 * B ^ 3 * C)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)) hCne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2B3C : ((A ^ 2 * B ^ 3 * C)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_A2B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2B2F : ((A ^ 2 * B ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hFne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2B2F : ((A ^ 2 * B ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_A2B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BCE : ((A ^ 2 * B * C * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne) hEne, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2BCE : ((A ^ 2 * B * C * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2C2D : ((A ^ 2 * C ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2C2D : ((A ^ 2 * C ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2EF : ((A ^ 2 * E * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hEne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hEne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_A2EF : ((A ^ 2 * E * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2EF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB5 : ((A * B ^ 5)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 5 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB5 : ((A * B ^ 5)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 5 := by
    rw [← hdeg_AB5, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3E : ((A * B ^ 3 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB3E : ((A * B ^ 3 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_AB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2CD : ((A * B ^ 2 * C * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne) hDne, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AB2CD : ((A * B ^ 2 * C * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_AB2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC3 : ((A * B * C ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 3 hCne), natDegree_mul hAne hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABC3 : ((A * B * C ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_ABC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCG : ((A * B * C * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hGne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABCG : ((A * B * C * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABDF : ((A * B * D * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABDF : ((A * B * D * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABE2 : ((A * B * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hEne), natDegree_mul hAne hBne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ABE2 : ((A * B * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_ABE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ACDE : ((A * C * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hCne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hCne) hDne, natDegree_mul hAne hCne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_ACDE : ((A * C * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ACDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AFG : ((A * F * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_AFG : ((A * F * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_AFG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C2 : ((B ^ 3 * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B3C2 : ((B ^ 3 * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2CF : ((B ^ 2 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hBne) hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2CF : ((B ^ 2 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_B2CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2E : ((B * C ^ 2 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hEne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BC2E : ((B * C ^ 2 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_BC2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD2 : ((B * C * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) (pow_ne_zero 2 hDne), natDegree_mul hBne hCne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BCD2 : ((B * C * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BCD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEG : ((B * E * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hGne, natDegree_mul hBne hEne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BEG : ((B * E * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BEG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_BF2 : ((B * F ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hFne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_BF2 : ((B * F ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_BF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CDG : ((C * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CEF : ((C * E * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hEne) hFne, natDegree_mul hCne hEne]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_CEF : ((C * E * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    clear * - hAB hAC hAD hAE hAF hAG
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3BC2, hcf_A3BG, hcf_A3CF, hcf_A3DE, hcf_A2B3C, hcf_A2B2F, hcf_A2BCE, hcf_A2BD2, hcf_A2C2D, hcf_A2DG, hcf_A2EF, hcf_AB5, hcf_AB3E, hcf_AB2CD, hcf_ABC3, hcf_ABCG, hcf_ABDF, hcf_ABE2, hcf_ACDE, hcf_AD3, hcf_AFG, hcf_B4D, hcf_B3C2, hcf_B3G, hcf_B2CF, hcf_B2DE, hcf_BC2E, hcf_BCD2, hcf_BEG, hcf_BF2, hcf_C3D, hcf_CDG, hcf_CEF, hcf_D2F, hcf_DE2]
  ring


/-! ## Inners and cores vanish on the cone -/

set_option maxHeartbeats 64000000 in
theorem quarticConeABCDEFG810_inners_eq_zero
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABCDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABCDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABCDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  exact ⟨hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner⟩

set_option maxHeartbeats 64000000 in
theorem quarticConeABCDEFG810_cores_eq_zero
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    quarticCoreMuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreNuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreXiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreOmicronABCDEFG810 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePrimitiveABCDEFG810 A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hinners := quarticConeABCDEFG810_inners_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hinners with ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0⟩
  have hmucore : quarticCoreMuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_mu
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hmu0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (800 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hnucore : quarticCoreNuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_nu
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hnu0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (6400 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hxicore : quarticCoreXiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_xi
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hxi0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (1600 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have homicroncore : quarticCoreOmicronABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_omicron
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hom0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (2560 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hpicore : quarticCorePiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_pi
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hpi0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (256000 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  have hprimitivecore : quarticCorePrimitiveABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticInner_ABCDEFG_sylvester_primitive
        A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff
        E.leadingCoeff F.leadingCoeff G.leadingCoeff
    rw [hk, hpr0] at hid
    simp only [mul_zero, add_zero] at hid
    have hcnt : (6400 : k) ≠ 0 := by norm_num
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · exact (hcnt h).elim
    · exact h
  exact ⟨hmucore, hnucore, hxicore, homicroncore, hpicore, hprimitivecore⟩


/-! ## a-resultants of the G-free cores, and the weight-26 factor T -/

set_option maxHeartbeats 64000000 in
def quarticCoreResA_mu_nuABCDEFG810 (b c d e f : k) : k :=
  (-14 : k) * b ^ 8 * d + 56 * b ^ 7 * c ^ 2 + (-320 : k) * b ^ 6 * c * f +
    96 * b ^ 6 * d * e + (-192 : k) * b ^ 5 * c ^ 2 * e +
    (-16 : k) * b ^ 5 * c * d ^ 2 + 384 * b ^ 5 * f ^ 2 +
    (-64 : k) * b ^ 4 * c ^ 3 * d + 1024 * b ^ 4 * c * e * f +
    (-64 : k) * b ^ 4 * d ^ 2 * f + (-128 : k) * b ^ 4 * d * e ^ 2 +
    384 * b ^ 3 * c * d ^ 2 * e + (-1024 : k) * b ^ 3 * e * f ^ 2 +
    1024 * b ^ 2 * c * d * f ^ 2 + 512 * b ^ 2 * d ^ 2 * e * f +
    512 * b * c * d ^ 3 * f + 512 * b * d ^ 4 * e

set_option maxHeartbeats 64000000 in
def quarticCoreResA_nu_xiABCDEFG810 (b c d e f : k) : k :=
  7 * b ^ 9 * c + (-12 : k) * b ^ 8 * f + (-52 : k) * b ^ 7 * c * e +
    10 * b ^ 7 * d ^ 2 + (-60 : k) * b ^ 6 * c ^ 2 * d + 80 * b ^ 6 * e * f +
    176 * b ^ 5 * c * d * f + 96 * b ^ 5 * c * e ^ 2 +
    (-32 : k) * b ^ 5 * d ^ 2 * e + 288 * b ^ 4 * c ^ 2 * d * e +
    (-48 : k) * b ^ 4 * c * d ^ 3 + (-128 : k) * b ^ 4 * d * f ^ 2 +
    (-128 : k) * b ^ 4 * e ^ 2 * f + (-768 : k) * b ^ 3 * c * d * e * f +
    384 * b ^ 2 * c ^ 2 * d ^ 2 * f + 384 * b ^ 2 * c * d ^ 3 * e +
    512 * b ^ 2 * d * e * f ^ 2 + (-512 : k) * b * c * d ^ 2 * f ^ 2 +
    (-512 : k) * b * d ^ 3 * e * f

set_option maxHeartbeats 64000000 in
def quarticCoreResA_nu_omicronABCDEFG810 (b c d e f : k) : k :=
  (-84 : k) * b ^ 12 * d ^ 2 + 280 * b ^ 11 * c ^ 2 * d +
    (-480 : k) * b ^ 10 * c * d * f + 640 * b ^ 10 * d ^ 2 * e +
    (-960 : k) * b ^ 9 * c ^ 2 * d * e + 320 * b ^ 9 * c * d ^ 3 +
    1280 * b ^ 8 * c * d * e * f + 1280 * b ^ 8 * d ^ 3 * f +
    (-1280 : k) * b ^ 8 * d ^ 2 * e ^ 2 + 1280 * b ^ 7 * c ^ 2 * d ^ 2 * f +
    1280 * b ^ 7 * c * d ^ 3 * e + (-640 : k) * b ^ 7 * d ^ 5 +
    (-5120 : k) * b ^ 6 * c * d ^ 2 * f ^ 2 +
    (-10240 : k) * b ^ 6 * d ^ 3 * e * f + 5120 * b ^ 5 * c * d ^ 4 * f +
    5120 * b ^ 5 * d ^ 5 * e

set_option maxHeartbeats 64000000 in
def quarticCoreT_ABCDEFG810 (b c d e f : k) : k :=
  7 * b ^ 6 * d + (-35 : k) * b ^ 5 * c ^ 2 + 340 * b ^ 4 * c * f +
    (-40 : k) * b ^ 4 * d * e + 120 * b ^ 3 * c ^ 2 * e +
    60 * b ^ 3 * c * d ^ 2 + (-480 : k) * b ^ 3 * f ^ 2 +
    80 * b ^ 2 * c ^ 3 * d + (-1120 : k) * b ^ 2 * c * e * f +
    240 * b ^ 2 * d ^ 2 * f + 160 * b * c ^ 2 * d * f +
    (-320 : k) * b * c * d ^ 2 * e + (-80 : k) * b * d ^ 4 +
    1280 * b * e * f ^ 2 + (-1920 : k) * c * d * f ^ 2 +
    (-1920 : k) * d ^ 2 * e * f

set_option maxHeartbeats 64000000 in
theorem quarticCore_resA_mu_nu
    (a b c d e f : k) :
    (8 * b ^ 3 * c + (-32 : k) * b ^ 2 * f + (-16 : k) * b * d ^ 2) *
        quarticCoreNuABCDEFG810 a b c d e f -
      (2 * b ^ 3 * d) * quarticCoreMuABCDEFG810 a b c d e f =
      quarticCoreResA_mu_nuABCDEFG810 b c d e f := by
  simp only [quarticCoreMuABCDEFG810, quarticCoreNuABCDEFG810,
    quarticCoreResA_mu_nuABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCore_resA_nu_xi
    (a b c d e f : k) :
    (2 * b ^ 3 * d) * quarticCoreXiABCDEFG810 a b c d e f -
      ((-1 : k) * b ^ 5 + 4 * b ^ 3 * e + 12 * b ^ 2 * c * d +
          (-16 : k) * b * d * f) *
        quarticCoreNuABCDEFG810 a b c d e f =
      quarticCoreResA_nu_xiABCDEFG810 b c d e f := by
  simp only [quarticCoreNuABCDEFG810, quarticCoreXiABCDEFG810,
    quarticCoreResA_nu_xiABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCore_resA_nu_omicron
    (a b c d e f : k) :
    (4 * b ^ 6 * d ^ 2) * quarticCoreOmicronABCDEFG810 a b c d e f -
      ((-20 : k) * a * b ^ 6 * d ^ 2 + (-40 : k) * b ^ 7 * c * d +
          160 * b ^ 5 * d ^ 3) *
        quarticCoreNuABCDEFG810 a b c d e f =
      quarticCoreResA_nu_omicronABCDEFG810 b c d e f := by
  simp only [quarticCoreNuABCDEFG810, quarticCoreOmicronABCDEFG810,
    quarticCoreResA_nu_omicronABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticCore_T_of_resA
    (b c d e f : k) :
    quarticCoreResA_nu_omicronABCDEFG810 b c d e f -
      (10 * b ^ 4 * d) * quarticCoreResA_mu_nuABCDEFG810 b c d e f =
      (8 * b ^ 6 * d) * quarticCoreT_ABCDEFG810 b c d e f := by
  simp only [quarticCoreResA_nu_omicronABCDEFG810,
    quarticCoreResA_mu_nuABCDEFG810, quarticCoreT_ABCDEFG810]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticConeABCDEFG810_afree_eq_zero
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    quarticCoreResA_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_omicronABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hcores := quarticConeABCDEFG810_cores_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hcores with ⟨hcmu, hcnu, hcxi, hcom, hcpi, hcpr⟩
  have hBne : B.leadingCoeff ≠ 0 := by
    intro h0
    have : B = 0 := leadingCoeff_eq_zero.mp h0
    have : B.natDegree = 0 := by simp [this]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hDne : D.leadingCoeff ≠ 0 := by
    intro h0
    have : D = 0 := leadingCoeff_eq_zero.mp h0
    have : D.natDegree = 0 := by simp [this]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, hAB, hAC, hAD, hAE, hAF, hAG⟩
    omega
  have hmn : quarticCoreResA_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resA_mu_nu A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcmu, hcnu] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hnx : quarticCoreResA_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resA_nu_xi A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcnu, hcxi] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hno : quarticCoreResA_nu_omicronABCDEFG810 B.leadingCoeff
      C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_resA_nu_omicron A.leadingCoeff B.leadingCoeff
        C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hcnu, hcom] at hid
    simp only [mul_zero, sub_zero] at hid
    exact hid.symm
  have hT : quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
      D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hid := quarticCore_T_of_resA B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff
    rw [hmn, hno] at hid
    simp only [mul_zero, sub_zero] at hid
    have h8 : (8 : k) ≠ 0 := by norm_num
    have hpowB : B.leadingCoeff ^ 6 ≠ 0 := pow_ne_zero 6 hBne
    have hmul := mul_eq_zero.mp hid.symm
    rcases hmul with h | h
    · have hmul2 := mul_eq_zero.mp h
      rcases hmul2 with h' | h'
      · have hmul3 := mul_eq_zero.mp h'
        rcases hmul3 with h8' | hB6
        · exact (h8 h8').elim
        · exact (hpowB hB6).elim
      · exact (hDne h').elim
    · exact h
  exact ⟨hmn, hnx, hno, hT⟩


/-! ## Residual: Groebner `(1)` not transcribed -/

set_option maxHeartbeats 64000000 in
theorem quarticConeABCDEFG810_residual
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    kappaQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      muQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      nuQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      xiQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      omicronQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      piQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      primitiveQuarticInnerABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 ∧
      quarticCoreMuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreNuABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreXiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreOmicronABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePiABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCorePrimitiveABCDEFG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_mu_nuABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_xiABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreResA_nu_omicronABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 ∧
      quarticCoreT_ABCDEFG810 B.leadingCoeff C.leadingCoeff
        D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
  have hinners := quarticConeABCDEFG810_inners_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hcores := quarticConeABCDEFG810_cores_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hafree := quarticConeABCDEFG810_afree_eq_zero (j := j) (t := t)
      l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  rcases hinners with ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0⟩
  rcases hcores with ⟨hcmu, hcnu, hcxi, hcom, hcpi, hcpr⟩
  rcases hafree with ⟨hmn, hnx, hno, hT⟩
  exact ⟨hk, hmu0, hnu0, hxi0, hom0, hpi0, hpr0, hcmu, hcnu, hcxi, hcom, hcpi, hcpr, hmn, hnx, hno, hT⟩

#print axioms quarticConeABCDEFG810_residual
#print axioms quarticConeABCDEFG810_inners_eq_zero
#print axioms quarticConeABCDEFG810_cores_eq_zero
#print axioms quarticConeABCDEFG810_afree_eq_zero
#print axioms quarticCore_resA_mu_nu
#print axioms quarticCore_resA_nu_xi
#print axioms quarticCore_resA_nu_omicron
#print axioms quarticCore_T_of_resA


end QuarticFullConeABCDEFG810

end Max11DegreeRoutes
